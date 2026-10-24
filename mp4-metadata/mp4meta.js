/*
 * mp4meta.js — MP4 / MOV (ISO BMFF) のメタデータを読み書きする小さなライブラリ。
 * moov ボックスだけをメモリに読み込み、映像・音声データ (mdat) は Blob.slice で
 * そのまま流用するため、大きなファイルでもメモリをほとんど使わない。
 */
(function (global) {
  'use strict';

  // 1904-01-01 (MP4 の時刻の起点) と 1970-01-01 の差 (秒)
  const MAC_EPOCH_OFFSET = 2082844800;
  const EMPTY = new Uint8Array(0);
  const CONTAINERS = new Set(['moov', 'trak', 'mdia', 'minf', 'stbl', 'udta', 'edts', 'dinf', 'mvex', 'ilst', 'meta']);
  const FREE_TYPES = new Set(['free', 'skip']);
  const MAX_FREE_REWRITE = 64 * 1024 * 1024;
  const enc = new TextEncoder();
  const dec = new TextDecoder('utf-8');

  // ---- バイト操作 ----

  function u16(b, o) { return (b[o] << 8) | b[o + 1]; }
  function u32(b, o) { return ((b[o] << 24) >>> 0) + (b[o + 1] << 16) + (b[o + 2] << 8) + b[o + 3]; }
  function u64(b, o) { return u32(b, o) * 4294967296 + u32(b, o + 4); }
  function putU32(b, o, v) {
    b[o] = (v >>> 24) & 255; b[o + 1] = (v >>> 16) & 255; b[o + 2] = (v >>> 8) & 255; b[o + 3] = v & 255;
  }
  function putU64(b, o, v) { putU32(b, o, Math.floor(v / 4294967296)); putU32(b, o + 4, v % 4294967296); }
  function fourcc(b, o) { return String.fromCharCode(b[o], b[o + 1], b[o + 2], b[o + 3]); }
  function fourccBytes(s) { return Uint8Array.of(s.charCodeAt(0), s.charCodeAt(1), s.charCodeAt(2), s.charCodeAt(3)); }
  function fourccToU32(s) { return u32(fourccBytes(s), 0); }
  function u32ToFourcc(v) { const b = new Uint8Array(4); putU32(b, 0, v); return fourcc(b, 0); }

  function concat(parts) {
    let n = 0;
    for (const p of parts) n += p.length;
    const out = new Uint8Array(n);
    let o = 0;
    for (const p of parts) { out.set(p, o); o += p.length; }
    return out;
  }

  // ---- ボックスの木 ----
  // { type, data: Uint8Array | null, children: Box[] | null, prefix, trailing }
  // コンテナは children を持ち、それ以外は data (ヘッダーを除いた中身) を持つ。

  function leaf(type, data) { return { type, data, children: null, prefix: EMPTY, trailing: EMPTY }; }
  function container(type, children, prefix) {
    return { type, data: null, children, prefix: prefix || EMPTY, trailing: EMPTY };
  }

  function parseBoxes(u8, start, end, parentType) {
    const boxes = [];
    let p = start;
    while (p + 8 <= end) {
      let size = u32(u8, p);
      const type = fourcc(u8, p + 4);
      let hdr = 8;
      if (size === 1) {
        if (p + 16 > end) return null;
        size = u64(u8, p + 8);
        hdr = 16;
      } else if (size === 0) {
        size = end - p;
      }
      if (size < hdr || p + size > end) return null;
      boxes.push(parseBox(u8, p, hdr, size, type, parentType));
      p += size;
    }
    return { boxes, trailing: u8.subarray(p, end) };
  }

  function parseBox(u8, p, hdr, size, type, parentType) {
    const payload = u8.subarray(p + hdr, p + size);
    const box = leaf(type, payload);
    if (!CONTAINERS.has(type) && parentType !== 'ilst') return box;
    let off = 0;
    if (type === 'meta') {
      // ISO の meta は version/flags を持つ FullBox、QuickTime の meta は持たない
      off = payload.length >= 8 && fourcc(payload, 4) === 'hdlr' ? 0 : 4;
    }
    const r = parseBoxes(payload, off, payload.length, type);
    if (!r) return box; // 解析できない場合は中身をそのまま保持する
    box.data = null;
    box.prefix = payload.subarray(0, off);
    box.children = r.boxes;
    box.trailing = r.trailing;
    return box;
  }

  function bodySize(b) {
    if (!b.children) return b.data.length;
    let n = b.prefix.length + b.trailing.length;
    for (const c of b.children) n += 8 + bodySize(c);
    return n;
  }

  function writeInto(b, out, p) {
    putU32(out, p, 8 + bodySize(b));
    for (let i = 0; i < 4; i++) out[p + 4 + i] = b.type.charCodeAt(i);
    p += 8;
    if (!b.children) { out.set(b.data, p); return p + b.data.length; }
    out.set(b.prefix, p); p += b.prefix.length;
    for (const c of b.children) p = writeInto(c, out, p);
    out.set(b.trailing, p);
    return p + b.trailing.length;
  }

  function serialize(b) {
    const out = new Uint8Array(8 + bodySize(b));
    writeInto(b, out, 0);
    return out;
  }

  function child(b, type) { return b && b.children ? b.children.find(c => c.type === type) || null : null; }
  function childrenOf(b, type) { return b && b.children ? b.children.filter(c => c.type === type) : []; }
  function path(b, ...types) { for (const t of types) b = child(b, t); return b; }

  function hdlrType(meta) {
    const h = child(meta, 'hdlr');
    return h && !h.children && h.data.length >= 12 ? fourcc(h.data, 8) : null;
  }

  function hdlrBox(handler, reserved) {
    const d = new Uint8Array(25); // version/flags, pre_defined, handler, reserved[3], 空の名前
    d.set(fourccBytes(handler), 8);
    if (reserved) d.set(fourccBytes(reserved), 12);
    return leaf('hdlr', d);
  }

  // ---- 時刻 ----

  function macToDate(s) { return s ? new Date((s - MAC_EPOCH_OFFSET) * 1000) : null; }
  function dateToMac(date) { return Math.round(date.getTime() / 1000) + MAC_EPOCH_OFFSET; }

  function readTimes(box) {
    const d = box.data;
    return d[0] === 1
      ? { creation: u64(d, 4), modification: u64(d, 12) }
      : { creation: u32(d, 4), modification: u32(d, 8) };
  }

  function writeTimes(box, creation, modification) {
    const d = box.data = box.data.slice();
    if (d[0] === 1) {
      if (creation != null) putU64(d, 4, creation);
      if (modification != null) putU64(d, 12, modification);
      return;
    }
    for (const v of [creation, modification]) {
      if (v != null && (v < 0 || v > 0xFFFFFFFF)) {
        throw new Error('この形式 (32bit) では 1904〜2040 年の日時しか保存できません');
      }
    }
    if (creation != null) putU32(d, 4, creation);
    if (modification != null) putU32(d, 8, modification);
  }

  // ---- iTunes 形式のタグ (moov/udta/meta[mdir]/ilst) ----

  function findItunesMeta(moov) {
    return childrenOf(child(moov, 'udta'), 'meta').find(m => hdlrType(m) === 'mdir') || null;
  }

  function itemText(item) {
    const data = child(item, 'data');
    if (!data || data.children || data.data.length < 8 || u32(data.data, 0) !== 1) return null;
    return dec.decode(data.data.subarray(8));
  }

  function textItem(type, text) {
    return container(type, [leaf('data', concat([Uint8Array.of(0, 0, 0, 1, 0, 0, 0, 0), enc.encode(text)]))]);
  }

  function readItunes(moov) {
    const tags = {};
    const ilst = child(findItunesMeta(moov), 'ilst');
    if (ilst) {
      for (const item of ilst.children) {
        if (item.children && !(item.type in tags)) tags[item.type] = itemText(item);
      }
    }
    return tags;
  }

  function ensureChild(parent, type, make) {
    let c = child(parent, type);
    if (!c) { c = make(); parent.children.push(c); }
    return c;
  }

  function applyItunes(moov, changes) {
    let ilst = child(findItunesMeta(moov), 'ilst');
    for (const [key, value] of Object.entries(changes)) {
      if (value === undefined) continue;
      if (!ilst && value !== '') {
        const udta = ensureChild(moov, 'udta', () => container('udta', []));
        let meta = findItunesMeta(moov);
        if (!meta) {
          meta = container('meta', [hdlrBox('mdir', 'appl')], new Uint8Array(4));
          udta.children.push(meta);
        }
        ilst = ensureChild(meta, 'ilst', () => container('ilst', []));
      }
      if (!ilst) continue;
      const remove = key === '©gen' ? ['©gen', 'gnre'] : [key];
      let pos = ilst.children.findIndex(c => remove.includes(c.type));
      ilst.children = ilst.children.filter(c => !remove.includes(c.type));
      if (value !== '') {
        if (pos < 0 || pos > ilst.children.length) pos = ilst.children.length;
        ilst.children.splice(pos, 0, textItem(key, value));
      }
    }
  }

  // ---- QuickTime 形式のメタデータ (moov/meta[mdta]: keys + ilst) ----

  // Apple は moov 直下、ffmpeg は moov/udta の中に置く
  function findMdtaMeta(moov) {
    const metas = childrenOf(moov, 'meta').concat(childrenOf(child(moov, 'udta'), 'meta'));
    return metas.find(m => hdlrType(m) === 'mdta') || null;
  }

  function removeBox(moov, box) {
    for (const parent of [moov, child(moov, 'udta')]) {
      if (parent) parent.children = parent.children.filter(c => c !== box);
    }
  }

  function readMdta(moov) {
    const meta = findMdtaMeta(moov);
    const keys = child(meta, 'keys');
    if (!keys || keys.children) return [];
    const d = keys.data;
    const entries = [];
    const count = d.length >= 8 ? u32(d, 4) : 0;
    let p = 8;
    for (let i = 0; i < count && p + 8 <= d.length; i++) {
      const size = u32(d, p);
      if (size < 8 || p + size > d.length) break;
      entries.push({ index: i + 1, ns: fourcc(d, p + 4), name: dec.decode(d.subarray(p + 8, p + size)), item: null });
      p += size;
    }
    for (const item of (child(meta, 'ilst') || { children: [] }).children) {
      const e = entries[fourccToU32(item.type) - 1];
      if (e && !e.item) e.item = item;
    }
    return entries.map(e => ({
      index: e.index,
      ns: e.ns,
      name: e.name,
      text: e.item ? itemText(e.item) : null,
      size: e.item ? bodySize(e.item) : 0,
      _item: e.item,
    }));
  }

  // list: [{ index (元の番号、新規は null), ns, name, text (undefined なら値はそのまま) }]
  // list に含まれない元のエントリは削除される。
  function applyMdta(moov, list) {
    const original = readMdta(moov);
    let meta = findMdtaMeta(moov);
    if (!list.length) {
      if (meta) removeBox(moov, meta);
      return;
    }
    if (!meta) {
      meta = container('meta', [hdlrBox('mdta')]);
      const udtaPos = moov.children.findIndex(c => c.type === 'udta');
      moov.children.splice(udtaPos < 0 ? moov.children.length : udtaPos, 0, meta);
    }
    const keyParts = [new Uint8Array(4), new Uint8Array(4)];
    const items = [];
    let n = 0;
    for (const e of list) {
      const orig = e.index != null ? original.find(o => o.index === e.index) : null;
      let item;
      if (e.text !== undefined) item = textItem('xxxx', e.text);
      else if (orig && orig._item) item = { ...orig._item };
      else continue;
      n++;
      const name = enc.encode(e.name);
      const k = new Uint8Array(8 + name.length);
      putU32(k, 0, k.length);
      k.set(fourccBytes(e.ns || 'mdta'), 4);
      k.set(name, 8);
      keyParts.push(k);
      item.type = u32ToFourcc(n);
      items.push(item);
    }
    putU32(keyParts[1], 0, n);
    const keys = leaf('keys', concat(keyParts));
    const ilst = container('ilst', items);
    const rest = meta.children.filter(c => c.type !== 'keys' && c.type !== 'ilst');
    const hdlrPos = rest.findIndex(c => c.type === 'hdlr');
    rest.splice(hdlrPos + 1, 0, keys, ilst);
    meta.children = rest;
  }

  // ---- udta の位置情報 (©xyz) ----

  function readXyz(moov) {
    const b = child(child(moov, 'udta'), '©xyz');
    if (!b || b.children || b.data.length < 4) return null;
    const len = u16(b.data, 0);
    return dec.decode(b.data.subarray(4, 4 + len));
  }

  function applyXyz(moov, value) {
    const udta = child(moov, 'udta');
    if (udta) udta.children = udta.children.filter(c => c.type !== '©xyz');
    if (!value) return;
    const s = enc.encode(value);
    const d = new Uint8Array(4 + s.length);
    d[0] = s.length >> 8; d[1] = s.length & 255;
    d[2] = 0x15; d[3] = 0xC7;
    d.set(s, 4);
    ensureChild(moov, 'udta', () => container('udta', [])).children.push(leaf('©xyz', d));
  }

  // 3GPP 形式の位置情報 (udta/loci)。ffmpeg や Android 端末が書き込む。
  function readLoci(moov) {
    const b = child(child(moov, 'udta'), 'loci');
    if (!b || b.children || b.data.length < 6) return null;
    const d = b.data;
    let p = 6;
    while (p < d.length && d[p] !== 0) p++;
    p += 2; // 名前の終端と role
    if (p + 12 > d.length) return null;
    const fixed = o => (u32(d, o) | 0) / 65536;
    return { longitude: fixed(p), latitude: fixed(p + 4), altitude: fixed(p + 8) };
  }

  // ---- 情報表示用 ----

  function langCode(v) {
    return String.fromCharCode(((v >> 10) & 31) + 0x60, ((v >> 5) & 31) + 0x60, (v & 31) + 0x60);
  }

  function readInfo(moov) {
    const mvhd = child(moov, 'mvhd');
    let duration = null;
    if (mvhd && !mvhd.children) {
      const d = mvhd.data;
      const ts = d[0] === 1 ? u32(d, 20) : u32(d, 12);
      const dur = d[0] === 1 ? u64(d, 24) : u32(d, 16);
      if (ts) duration = dur / ts;
    }
    const tracks = childrenOf(moov, 'trak').map(trak => {
      const t = { handler: null, codec: null, width: null, height: null, language: null };
      const tkhd = child(trak, 'tkhd');
      if (tkhd && !tkhd.children && tkhd.data.length >= 8) {
        const d = tkhd.data;
        t.width = Math.round(u32(d, d.length - 8) / 65536);
        t.height = Math.round(u32(d, d.length - 4) / 65536);
      }
      t.handler = hdlrType(child(trak, 'mdia'));
      const mdhd = path(trak, 'mdia', 'mdhd');
      if (mdhd && !mdhd.children) t.language = langCode(u16(mdhd.data, mdhd.data[0] === 1 ? 32 : 20));
      const stsd = path(trak, 'mdia', 'minf', 'stbl', 'stsd');
      if (stsd && !stsd.children && stsd.data.length >= 16) t.codec = fourcc(stsd.data, 12);
      return t;
    });
    return { duration, tracks };
  }

  function outline(box, depth, out) {
    out.push({ depth, type: box.type, size: 8 + bodySize(box) });
    if (box.children) for (const c of box.children) outline(c, depth + 1, out);
    return out;
  }

  // ---- ファイル全体 ----

  async function readBytes(blob, start, end) {
    return new Uint8Array(await blob.slice(start, end).arrayBuffer());
  }

  async function scanTop(file) {
    const boxes = [];
    let p = 0;
    let moovIndex = -1;
    while (p + 8 <= file.size) {
      const h = await readBytes(file, p, Math.min(p + 16, file.size));
      let size = u32(h, 0);
      const type = fourcc(h, 4);
      let hdr = 8;
      if (size === 1) { size = u64(h, 8); hdr = 16; } else if (size === 0) size = file.size - p;
      if (size < hdr || p + size > file.size) throw new Error(`壊れたボックスがあります (${JSON.stringify(type)}, 位置 ${p})`);
      boxes.push({ type, start: p, size, hdr });
      if (type === 'moov') moovIndex = boxes.length - 1;
      p += size;
      if (moovIndex >= 0 && boxes.length > moovIndex + 1) break; // moov の次のボックスまで分かれば十分
    }
    return { boxes, moovIndex };
  }

  function parseMoov(bytes, hdr) {
    const moov = parseBox(bytes, 0, hdr, bytes.length, 'moov', null);
    if (!moov.children) throw new Error('moov ボックスを解析できませんでした');
    return moov;
  }

  async function load(file) {
    const { boxes, moovIndex } = await scanTop(file);
    if (moovIndex < 0) throw new Error('moov ボックスが見つかりません。MP4 / MOV ファイルではない可能性があります。');
    const top = boxes[moovIndex];
    const moovBytes = await readBytes(file, top.start, top.start + top.size);
    const moov = parseMoov(moovBytes, top.hdr);
    const ftypBox = boxes.find(b => b.type === 'ftyp');
    let brand = null;
    if (ftypBox) {
      const f = await readBytes(file, ftypBox.start, ftypBox.start + Math.min(ftypBox.size, 64));
      brand = fourcc(f, ftypBox.hdr);
    }
    const mvhd = child(moov, 'mvhd');
    if (!mvhd || mvhd.children) throw new Error('mvhd ボックスが見つかりません');
    const times = readTimes(mvhd);
    return {
      file,
      moovStart: top.start,
      moovSize: top.size,
      moovHdr: top.hdr,
      moovBytes,
      moovAtEnd: moovIndex === boxes.length - 1,
      nextBox: boxes[moovIndex + 1] || null,
      fragmented: !!child(moov, 'mvex'),
      brand,
      info: readInfo(moov),
      creation: macToDate(times.creation),
      modification: macToDate(times.modification),
      itunes: readItunes(moov),
      mdta: readMdta(moov).map(({ _item, ...e }) => e),
      xyz: readXyz(moov),
      loci: readLoci(moov),
      outline: outline(moov, 0, []),
    };
  }

  function patchChunkOffsets(box, from, delta) {
    if (box.children) { for (const c of box.children) patchChunkOffsets(c, from, delta); return; }
    if (box.type !== 'stco' && box.type !== 'co64') return;
    const d = box.data = box.data.slice();
    const count = u32(d, 4);
    const wide = box.type === 'co64';
    for (let i = 0; i < count; i++) {
      const o = 8 + i * (wide ? 8 : 4);
      const v = wide ? u64(d, o) : u32(d, o);
      if (v < from) continue;
      if (wide) putU64(d, o, v + delta);
      else if (v + delta > 0xFFFFFFFF) throw new Error('チャンク位置が 4GB を超えるため保存できません');
      else putU32(d, o, v + delta);
    }
  }

  /*
   * edits:
   *   creation, modification : Date (省略時は変更しない)
   *   applyToTracks          : true ならトラック (tkhd / mdhd) の日時も同じ値にする
   *   itunes                 : { '©nam': '新しい値' | '' (削除) }
   *   mdta                   : applyMdta の list (省略時は変更しない)
   *   xyz                    : 文字列 | '' (削除) (省略時は変更しない)
   *   removeLoci             : true なら udta/loci を削除
   */
  function applyEdits(doc, edits) {
    const moov = parseMoov(doc.moovBytes, doc.moovHdr);
    if (edits.creation || edits.modification) {
      const c = edits.creation ? dateToMac(edits.creation) : null;
      const m = edits.modification ? dateToMac(edits.modification) : null;
      const targets = [child(moov, 'mvhd')];
      if (edits.applyToTracks) {
        for (const trak of childrenOf(moov, 'trak')) targets.push(child(trak, 'tkhd'), path(trak, 'mdia', 'mdhd'));
      }
      for (const b of targets) if (b && !b.children) writeTimes(b, c, m);
    }
    if (edits.itunes) applyItunes(moov, edits.itunes);
    if (edits.mdta) applyMdta(moov, edits.mdta);
    if (edits.xyz !== undefined) applyXyz(moov, edits.xyz);
    if (edits.removeLoci) {
      const udta = child(moov, 'udta');
      if (udta) udta.children = udta.children.filter(c => c.type !== 'loci');
    }
    return moov;
  }

  function save(doc, edits) {
    const moov = applyEdits(doc, edits);
    // 以前の編集で入れた余白 (free) はいったん外し、必要なら作り直す
    moov.children = moov.children.filter(c => !FREE_TYPES.has(c.type));
    let delta = 8 + bodySize(moov) - doc.moovSize;
    let tailStart = doc.moovStart + doc.moovSize;
    let filler = null;
    let method = 'none';

    if (delta < 0 && -delta >= 8) {
      // 小さくなった分を moov 内の free で埋め、後ろのデータ位置を変えない
      moov.children.push(leaf('free', new Uint8Array(-delta - 8)));
      delta = 0;
      method = 'padding';
    } else if (delta > 0 && doc.nextBox && FREE_TYPES.has(doc.nextBox.type)) {
      // 直後の free を削って大きくなった分を吸収する
      const left = doc.nextBox.size - delta;
      if (left === 0 || (left >= 8 && left <= MAX_FREE_REWRITE)) {
        if (left) { filler = new Uint8Array(left); putU32(filler, 0, left); filler.set(fourccBytes('free'), 4); }
        tailStart += doc.nextBox.size;
        delta = 0;
        method = 'free';
      }
    }
    if (delta !== 0) {
      if (doc.fragmented) {
        throw new Error('断片化 MP4 (fMP4) ではメタデータのサイズを増やせません。値を短くしてみてください。');
      }
      patchChunkOffsets(moov, doc.moovStart, delta);
      method = 'offsets';
    }
    const parts = [doc.file.slice(0, doc.moovStart), serialize(moov)];
    if (filler) parts.push(filler);
    parts.push(doc.file.slice(tailStart));
    return { blob: new Blob(parts, { type: doc.file.type || 'video/mp4' }), method, delta };
  }

  const api = { load, save, MAC_EPOCH_OFFSET };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else global.MP4Meta = api;
})(typeof self !== 'undefined' ? self : this);
