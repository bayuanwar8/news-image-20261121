// news-image-20261121 — Saturday 21 November 2026 in one image.
// A Node 22 program (standard library only). Draws a one-page newspaper
// front page from scratch: masthead, stat strip, three hero stories
// (Zelensky as a big named figure, COP31, Riyadh), ten pictured stories,
// a "WHERE IT HAPPENED" world map with numbered pins, 22 briefs, and a
// DATE CHECK box. Deterministic: no clock, no unseeded randomness —
// two runs write byte-identical PNGs. No network.
import * as fs from "node:fs";
import * as path from "node:path";
import * as zlib from "node:zlib";
import { fileURLToPath } from "node:url";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const OUT = process.env.MAKEFUN_OUTPUT_DIR || path.join(HERE, "out");
const W = 1024;
const H = 1024;

// ---- seeded PRNG (mulberry32), deterministic grain only ----
function mulberry32(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// ---- minimal deterministic PNG encoder (RGB, 8-bit) ----
const CRC_TAB: Uint32Array = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c >>> 0;
  }
  return t;
})();

function crc32(buf: Uint8Array): number {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC_TAB[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}

function pngChunk(type: string, data: Uint8Array): Buffer {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, "ascii");
  out.set(data, 8);
  out.writeUInt32BE(crc32(out.subarray(4, 8 + data.length)), 8 + data.length);
  return out;
}

function encodePNG(w: number, h: number, rgb: Uint8Array): Buffer {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(w, 0);
  ihdr.writeUInt32BE(h, 4);
  ihdr[8] = 8; // bit depth
  ihdr[9] = 2; // color type 2 = RGB
  // raw scanlines, filter 0 (this image is noise-grained: filters cost bytes)
  const raw = new Uint8Array(h * (1 + w * 3));
  for (let y = 0; y < h; y++) {
    raw[y * (1 + w * 3)] = 0;
    raw.set(rgb.subarray(y * w * 3, (y + 1) * w * 3), y * (1 + w * 3) + 1);
  }
  const idat = zlib.deflateSync(raw, { level: 6 });
  return Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    pngChunk("IHDR", ihdr),
    pngChunk("IDAT", idat),
    pngChunk("IEND", new Uint8Array(0)),
  ]);
}

// ---- TrueType reader: glyph outlines -> antialiased bitmaps ----
type Pt = [number, number];
// A segment is a line (2 points) or a quadratic bezier (3 points).
type Seg = Pt[]; // length 2 or 3
interface GlyphBits {
  w: number;
  h: number;
  dx: number; // left bearing in px (from pen x)
  dy: number; // top offset in px (from baseline)
  adv: number; // advance width in px
  alpha: Uint8Array; // w*h, 0..255
}

function rdU16(b: Buffer, o: number): number { return b.readUInt16BE(o); }
function rdI16(b: Buffer, o: number): number { return b.readInt16BE(o); }
function rdU32(b: Buffer, o: number): number { return b.readUInt32BE(o); }

export class TTF {
  upm: number;
  numGlyphs: number;
  idxToLoc: number;
  numHMet: number;
  cmap: Map<number, number>;
  hmtx: Buffer;
  loca: Buffer;
  glyf: Buffer;

  constructor(file: string) {
    const b = fs.readFileSync(file);
    const nTab = rdU16(b, 4);
    const tabs = new Map<string, { off: number; len: number }>();
    for (let i = 0; i < nTab; i++) {
      const o = 12 + i * 16;
      tabs.set(b.toString("ascii", o, o + 4), { off: rdU32(b, o + 8), len: rdU32(b, o + 12) });
    }
    const need = (t: string) => {
      const x = tabs.get(t);
      if (!x) throw new Error("TTF missing table " + t + " in " + file);
      return x;
    };
    const head = need("head");
    const maxp = need("maxp");
    const hhea = need("hhea");
    const hmtxT = need("hmtx");
    const locaT = need("loca");
    const glyfT = need("glyf");
    const cmapT = need("cmap");
    this.upm = rdU16(b, head.off + 18);
    this.idxToLoc = rdI16(b, head.off + 50);
    this.numGlyphs = rdU16(b, maxp.off + 4);
    this.numHMet = rdU16(b, hhea.off + 34);
    this.hmtx = b.subarray(hmtxT.off, hmtxT.off + hmtxT.len);
    this.loca = b.subarray(locaT.off, locaT.off + locaT.len);
    this.glyf = b.subarray(glyfT.off, glyfT.off + glyfT.len);
    this.cmap = this.readCmap4(b, cmapT.off);
  }

  private readCmap4(b: Buffer, base: number): Map<number, number> {
    const out = new Map<number, number>();
    const nSub = rdU16(b, base + 2);
    let fmt4 = -1;
    for (let i = 0; i < nSub; i++) {
      const plat = rdU16(b, base + 4 + i * 8);
      const enc = rdU16(b, base + 6 + i * 8);
      const off = rdU32(b, base + 8 + i * 8);
      if (rdU16(b, base + off) === 4 && (plat === 3 || plat === 0) && fmt4 < 0) fmt4 = base + off;
    }
    if (fmt4 < 0) return out;
    const segCount = rdU16(b, fmt4 + 6) / 2;
    const endBase = fmt4 + 14;
    const startBase = endBase + segCount * 2 + 2;
    const deltaBase = startBase + segCount * 2;
    const rangeBase = deltaBase + segCount * 2;
    for (let s = 0; s < segCount; s++) {
      const end = rdU16(b, endBase + s * 2);
      const start = rdU16(b, startBase + s * 2);
      const delta = rdI16(b, deltaBase + s * 2);
      const rangeOff = rdU16(b, rangeBase + s * 2);
      for (let cp = start; cp <= end && cp < 0xffff; cp++) {
        let gid = 0;
        if (rangeOff === 0) gid = (cp + delta) & 0xffff;
        else {
          const gi = rdU16(b, rangeBase + s * 2 + rangeOff + (cp - start) * 2);
          gid = gi === 0 ? 0 : (gi + delta) & 0xffff;
        }
        if (gid) out.set(cp, gid);
      }
    }
    return out;
  }

  private glyphOffset(gid: number): [number, number] {
    if (this.idxToLoc === 1) {
      return [rdU32(this.loca, gid * 4), rdU32(this.loca, (gid + 1) * 4)];
    }
    return [rdU16(this.loca, gid * 2) * 2, rdU16(this.loca, (gid + 1) * 2) * 2];
  }

  advance(gid: number): number {
    const i = Math.min(gid, this.numHMet - 1);
    return rdU16(this.hmtx, i * 4);
  }

  // Collect outline segments for a glyph (simple + composite), in font units.
  // Each contour becomes a list of segments; points are absolute.
  private collect(gid: number, segs: Seg[], depth: number): void {
    if (depth > 4) return;
    const [g0, g1] = this.glyphOffset(gid);
    if (g1 <= g0) return;
    const g = this.glyf;
    const nCon = rdI16(g, g0);
    if (nCon >= 0) {
      let p = g0 + 10;
      const ends: number[] = [];
      for (let i = 0; i < nCon; i++) ends.push(rdU16(g, p + i * 2));
      p += nCon * 2;
      const nIns = rdU16(g, p);
      p += 2 + nIns;
      const nPts = nCon ? ends[nCon - 1] + 1 : 0;
      const flags: number[] = [];
      while (flags.length < nPts) {
        const f = g[p++];
        flags.push(f);
        if (f & 0x08) {
          const rep = g[p++];
          for (let i = 0; i < rep; i++) flags.push(f);
        }
      }
      const xs: number[] = [];
      let x = 0;
      for (let i = 0; i < nPts; i++) {
        const f = flags[i];
        if (f & 0x02) { const d = g[p++]; x += f & 0x10 ? d : -d; }
        else if (!(f & 0x10)) { x += rdI16(g, p); p += 2; }
        xs.push(x);
      }
      const ys: number[] = [];
      let y = 0;
      for (let i = 0; i < nPts; i++) {
        const f = flags[i];
        if (f & 0x04) { const d = g[p++]; y += f & 0x20 ? d : -d; }
        else if (!(f & 0x20)) { y += rdI16(g, p); p += 2; }
        ys.push(y);
      }
      let start = 0;
      for (const end of ends) {
        const pts: { x: number; y: number; on: boolean }[] = [];
        for (let i = start; i <= end; i++) pts.push({ x: xs[i], y: ys[i], on: (flags[i] & 0x01) !== 0 });
        this.contourSegs(pts, segs);
        start = end + 1;
      }
      return;
    }
    // composite glyph
    let p = g0 + 10;
    for (;;) {
      const cFlags = rdU16(g, p);
      const comp = rdU16(g, p + 2);
      p += 4;
      let dx = 0, dy = 0;
      if (cFlags & 0x0001) { dx = rdI16(g, p); dy = rdI16(g, p + 2); p += 4; }
      else { p += 2; } // point matching: ignore, treat as 0,0
      let sx = 1, sy = 1, s01 = 0, s10 = 0;
      if (cFlags & 0x0008) { sx = sy = rdI16(g, p) / 16384; p += 2; }
      else if (cFlags & 0x0040) { sx = rdI16(g, p) / 16384; sy = rdI16(g, p + 2) / 16384; p += 4; }
      else if (cFlags & 0x0080) { sx = rdI16(g, p) / 16384; s01 = rdI16(g, p + 2) / 16384; s10 = rdI16(g, p + 4) / 16384; sy = rdI16(g, p + 6) / 16384; p += 8; }
      const before = segs.length;
      this.collect(comp, segs, depth + 1);
      for (let i = before; i < segs.length; i++) {
        for (const pt of segs[i]) {
          const nx = pt[0] * sx + pt[1] * s10 + dx;
          const ny = pt[0] * s01 + pt[1] * sy + dy;
          pt[0] = nx; pt[1] = ny;
        }
      }
      if (!(cFlags & 0x0020)) break;
    }
  }

  private contourSegs(pts: { x: number; y: number; on: boolean }[], segs: Seg[]): void {
    if (pts.length === 0) return;
    // find a starting on-curve point (or implied midpoint)
    let si = 0;
    while (si < pts.length && !pts[si].on) si++;
    const start: Pt = si < pts.length
      ? [pts[si].x, pts[si].y]
      : [(pts[0].x + pts[pts.length - 1].x) / 2, (pts[0].y + pts[pts.length - 1].y) / 2];
    let cur: Pt = start;
    let i = si < pts.length ? si : 0;
    const n = pts.length;
    for (let step = 0; step < n; step++) {
      const idx = (i + step) % n;
      const pt = pts[idx];
      if (pt.on) {
        if (pt.x !== cur[0] || pt.y !== cur[1]) segs.push([cur, [pt.x, pt.y]]);
        cur = [pt.x, pt.y];
      } else {
        const nxt = pts[(idx + 1) % n];
        const end: Pt = nxt.on
          ? [nxt.x, nxt.y]
          : [(pt.x + nxt.x) / 2, (pt.y + nxt.y) / 2];
        segs.push([cur, [pt.x, pt.y], end]);
        cur = end;
        if (!nxt.on) step++; // consumed the next off-curve point via midpoint
      }
    }
    if (cur[0] !== start[0] || cur[1] !== start[1]) segs.push([cur, start]);
  }

  // Rasterize one glyph at a pixel size, supersampled 2x, cached by caller.
  rasterize(cp: number, px: number): GlyphBits | null {
    const gid = this.cmap.get(cp) || 0;
    if (gid === 0) return null;
    const segs: Seg[] = [];
    this.collect(gid, segs, 0);
    const scale = (px / this.upm) * 2; // supersample 2x
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (const s of segs) for (const [x, y] of s) {
      if (x < x0) x0 = x; if (x > x1) x1 = x;
      if (y < y0) y0 = y; if (y > y1) y1 = y;
    }
    if (!isFinite(x0)) return { w: 0, h: 0, dx: 0, dy: 0, adv: (this.advance(gid) * px) / this.upm, alpha: new Uint8Array(0) };
    // flatten quadratics into line edges
    const edges: [number, number, number, number][] = [];
    for (const s of segs) {
      if (s.length === 2) {
        edges.push([s[0][0] * scale, s[0][1] * scale, s[1][0] * scale, s[1][1] * scale]);
      } else {
        const [a, c, b] = s;
        let px0 = a[0] * scale, py0 = a[1] * scale;
        const steps = 8;
        for (let k = 1; k <= steps; k++) {
          const t = k / steps;
          const mt = 1 - t;
          const qx = (mt * mt * a[0] + 2 * mt * t * c[0] + t * t * b[0]) * scale;
          const qy = (mt * mt * a[1] + 2 * mt * t * c[1] + t * t * b[1]) * scale;
          edges.push([px0, py0, qx, qy]);
          px0 = qx; py0 = qy;
        }
      }
    }
    const minX = Math.floor(x0 * scale);
    const maxX = Math.ceil(x1 * scale);
    const minY = Math.floor(y0 * scale);
    const maxY = Math.ceil(y1 * scale);
    const sw = Math.max(1, maxX - minX);
    const sh = Math.max(1, maxY - minY);
    const sup = new Uint8Array(sw * sh); // 0/1 coverage at 2x
    for (let yy = 0; yy < sh; yy++) {
      // font y runs UP; bitmap row 0 is the TOP, so scan from maxY down
      const yc = maxY - yy - 0.5;
      const xs: number[] = [];
      for (const [ax, ay, bx, by] of edges) {
        if ((ay <= yc && yc < by) || (by <= yc && yc < ay)) {
          xs.push(ax + ((yc - ay) * (bx - ax)) / (by - ay));
        }
      }
      xs.sort((a, b) => a - b);
      for (let k = 0; k + 1 < xs.length; k += 2) {
        const xa = Math.max(0, Math.ceil(xs[k] - minX));
        const xb = Math.min(sw - 1, Math.floor(xs[k + 1] - minX));
        for (let x = xa; x <= xb; x++) sup[yy * sw + x] = 1;
      }
    }
    // downsample 2x2 -> alpha
    const w = Math.ceil(sw / 2);
    const h = Math.ceil(sh / 2);
    const alpha = new Uint8Array(w * h);
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        let sum = 0;
        for (let dy = 0; dy < 2; dy++) for (let dx = 0; dx < 2; dx++) {
          const sx = x * 2 + dx, sy = y * 2 + dy;
          if (sx < sw && sy < sh) sum += sup[sy * sw + sx];
        }
        alpha[y * w + x] = Math.round((sum / 4) * 255);
      }
    }
    return {
      w, h,
      dx: Math.floor(minX / 2),
      dy: -Math.ceil(maxY / 2),
      adv: (this.advance(gid) * px) / this.upm,
      alpha,
    };
  }
}

const glyphCache = new Map<string, GlyphBits | null>();
const fontIds = new WeakMap<TTF, string>();
let nextFontId = 0;
function glyphBits(font: TTF, px: number, cp: number): GlyphBits | null {
  let fid = fontIds.get(font);
  if (fid === undefined) { fid = "F" + (nextFontId++); fontIds.set(font, fid); }
  const key = fid + "|" + px + "|" + cp;
  let g = glyphCache.get(key);
  if (g === undefined) {
    g = font.rasterize(cp, px);
    glyphCache.set(key, g);
  }
  return g;
}

// ---- fonts ----
const serifB = new TTF(path.join(HERE, "fonts", "DejaVuSerif-Bold.ttf"));
const serif = new TTF(path.join(HERE, "fonts", "DejaVuSerif.ttf"));
const sansB = new TTF(path.join(HERE, "fonts", "DejaVuSans-Bold.ttf"));
const sans = new TTF(path.join(HERE, "fonts", "DejaVuSans.ttf"));

// ---- palette (cream paper, saturated inks) ----
type RGB = [number, number, number];
const PAPER: RGB = [246, 238, 219];
const PAPER2: RGB = [240, 230, 205];
const INK: RGB = [26, 22, 18];
const RED: RGB = [186, 32, 38];
const REDDK: RGB = [150, 20, 26];
const NAVY: RGB = [16, 28, 51];
const NAVY2: RGB = [28, 44, 78];
const SKY: RGB = [178, 214, 235];
const SKYDK: RGB = [120, 170, 210];
const GOLD: RGB = [212, 160, 32];
const GREEN: RGB = [46, 125, 79];
const TEAL: RGB = [42, 138, 138];
const ORANGE: RGB = [201, 123, 30];
const PURPLE: RGB = [106, 74, 158];
const BLUE: RGB = [31, 78, 156];
const WHITE: RGB = [255, 255, 255];
const CREAM: RGB = [250, 244, 228];
const GREY: RGB = [110, 104, 92];
const SKIN: RGB = [214, 164, 120];
const SKIN2: RGB = [198, 142, 96];
const HAIR: RGB = [74, 60, 48];

// ---- canvas ----
class Canvas {
  readonly buf: Uint8Array;
  constructor() {
    this.buf = new Uint8Array(W * H * 3);
    for (let i = 0; i < this.buf.length; i += 3) {
      this.buf[i] = PAPER[0]; this.buf[i + 1] = PAPER[1]; this.buf[i + 2] = PAPER[2];
    }
  }
  px(x: number, y: number, c: RGB): void {
    if (x < 0 || y < 0 || x >= W || y >= H) return;
    const i = (y * W + x) * 3;
    this.buf[i] = c[0]; this.buf[i + 1] = c[1]; this.buf[i + 2] = c[2];
  }
  blend(x: number, y: number, c: RGB, a: number): void {
    if (a <= 0 || x < 0 || y < 0 || x >= W || y >= H) return;
    if (a >= 1) { this.px(x, y, c); return; }
    const i = (y * W + x) * 3;
    const ia = 1 - a;
    this.buf[i] = Math.round(c[0] * a + this.buf[i] * ia);
    this.buf[i + 1] = Math.round(c[1] * a + this.buf[i + 1] * ia);
    this.buf[i + 2] = Math.round(c[2] * a + this.buf[i + 2] * ia);
  }
  rect(x: number, y: number, w: number, h: number, c: RGB): void {
    const x0 = Math.max(0, Math.round(x)), y0 = Math.max(0, Math.round(y));
    const x1 = Math.min(W, Math.round(x + w)), y1 = Math.min(H, Math.round(y + h));
    for (let yy = y0; yy < y1; yy++) {
      let i = (yy * W + x0) * 3;
      for (let xx = x0; xx < x1; xx++) {
        this.buf[i] = c[0]; this.buf[i + 1] = c[1]; this.buf[i + 2] = c[2]; i += 3;
      }
    }
  }
  strokeRect(x: number, y: number, w: number, h: number, c: RGB, t = 1): void {
    this.rect(x, y, w, t, c);
    this.rect(x, y + h - t, w, t, c);
    this.rect(x, y, t, h, c);
    this.rect(x + w - t, y, t, h, c);
  }
  hline(x: number, y: number, w: number, c: RGB): void { this.rect(x, y, w, 1, c); }
  vline(x: number, y: number, h: number, c: RGB): void { this.rect(x, y, 1, h, c); }
  line(x0: number, y0: number, x1: number, y1: number, c: RGB, w = 1): void {
    const dx = x1 - x0, dy = y1 - y0;
    const len = Math.max(Math.abs(dx), Math.abs(dy));
    const steps = Math.max(1, Math.ceil(len * 2));
    const r = w / 2;
    for (let s = 0; s <= steps; s++) {
      const t = s / steps;
      this.rect(x0 + dx * t - r, y0 + dy * t - r, w, w, c);
    }
  }
  circle(cx: number, cy: number, r: number, c: RGB): void {
    const x0 = Math.max(0, Math.floor(cx - r)), x1 = Math.min(W - 1, Math.ceil(cx + r));
    const y0 = Math.max(0, Math.floor(cy - r)), y1 = Math.min(H - 1, Math.ceil(cy + r));
    for (let y = y0; y <= y1; y++) {
      const dy = y + 0.5 - cy;
      const hw = Math.sqrt(Math.max(0, r * r - dy * dy));
      const xa = Math.max(x0, Math.ceil(cx - hw)), xb = Math.min(x1, Math.floor(cx + hw));
      for (let x = xa; x <= xb; x++) this.px(x, y, c);
    }
  }
  ring(cx: number, cy: number, r: number, c: RGB, t = 2): void {
    for (let k = 0; k < t; k++) {
      const rr = r - k;
      const steps = Math.max(24, Math.floor(2 * Math.PI * rr));
      for (let s = 0; s < steps; s++) {
        const a = (s / steps) * Math.PI * 2;
        this.px(Math.round(cx + Math.cos(a) * rr), Math.round(cy + Math.sin(a) * rr), c);
      }
    }
  }
  poly(pts: [number, number][], c: RGB): void {
    if (pts.length < 3) return;
    let yMin = Infinity, yMax = -Infinity;
    for (const [, y] of pts) { if (y < yMin) yMin = y; if (y > yMax) yMax = y; }
    const xs: number[] = [];
    for (let y = Math.max(0, Math.floor(yMin)); y <= Math.min(H - 1, Math.ceil(yMax)); y++) {
      const yc = y + 0.5;
      xs.length = 0;
      for (let i = 0; i < pts.length; i++) {
        const [ax, ay] = pts[i], [bx, by] = pts[(i + 1) % pts.length];
        if ((ay <= yc && yc < by) || (by <= yc && yc < ay)) {
          xs.push(ax + ((yc - ay) * (bx - ax)) / (by - ay));
        }
      }
      xs.sort((a, b) => a - b);
      for (let k = 0; k + 1 < xs.length; k += 2) {
        const xa = Math.max(0, Math.ceil(xs[k])), xb = Math.min(W - 1, Math.floor(xs[k + 1]));
        for (let x = xa; x <= xb; x++) this.px(x, y, c);
      }
    }
  }
  ellipse(cx: number, cy: number, rx: number, ry: number, c: RGB): void {
    const steps = 48;
    const pts: [number, number][] = [];
    for (let s = 0; s < steps; s++) {
      const a = (s / steps) * Math.PI * 2;
      pts.push([cx + Math.cos(a) * rx, cy + Math.sin(a) * ry]);
    }
    this.poly(pts, c);
  }
  // deterministic grain over a region (adds file weight + paper texture)
  grain(x: number, y: number, w: number, h: number, amt: number, seed: number): void {
    const rnd = mulberry32(seed);
    for (let yy = Math.max(0, y); yy < Math.min(H, y + h); yy++) {
      for (let xx = Math.max(0, x); xx < Math.min(W, x + w); xx++) {
        const d = Math.floor((rnd() - 0.5) * 2 * amt);
        if (d === 0) continue;
        const i = (yy * W + xx) * 3;
        this.buf[i] = Math.max(0, Math.min(255, this.buf[i] + d));
        this.buf[i + 1] = Math.max(0, Math.min(255, this.buf[i + 1] + d));
        this.buf[i + 2] = Math.max(0, Math.min(255, this.buf[i + 2] + d));
      }
    }
  }
  // ---- text ----
  measure(font: TTF, size: number, text: string): number {
    let w = 0;
    for (const ch of text) {
      const g = glyphBits(font, size, ch.codePointAt(0) as number);
      w += g ? g.adv : size * 0.5;
    }
    return w;
  }
  text(font: TTF, size: number, x: number, baseY: number, s: string, c: RGB, align: "l" | "c" | "r" = "l", shear = 0): void {
    let pen = x;
    if (align === "c") pen = x - this.measure(font, size, s) / 2;
    else if (align === "r") pen = x - this.measure(font, size, s);
    for (const ch of s) {
      const cp = ch.codePointAt(0) as number;
      const g = glyphBits(font, size, cp);
      if (g && g.w > 0) {
        const gx = Math.round(pen) + g.dx;
        const gy = Math.round(baseY) + g.dy;
        for (let py = 0; py < g.h; py++) {
          for (let px = 0; px < g.w; px++) {
            const a = g.alpha[py * g.w + px];
            if (a) this.blend(gx + px + Math.round(shear * (baseY - (gy + py))), gy + py, c, a / 255);
          }
        }
      }
      pen += g ? g.adv : size * 0.5;
    }
  }
  wrap(font: TTF, size: number, s: string, maxW: number): string[] {
    const words = s.split(/\s+/).filter((w) => w.length > 0);
    const lines: string[] = [];
    let cur = "";
    for (const w of words) {
      const trial = cur ? cur + " " + w : w;
      if (this.measure(font, size, trial) <= maxW) { cur = trial; continue; }
      if (cur) lines.push(cur);
      let piece = "";
      for (const ch of w) {
        if (this.measure(font, size, piece + ch) <= maxW) piece += ch;
        else { if (piece) lines.push(piece); piece = ch; }
      }
      cur = piece;
    }
    if (cur) lines.push(cur);
    return lines.length ? lines : [""];
  }
  para(font: TTF, size: number, x: number, y: number, s: string, maxW: number, lh: number, c: RGB, maxLines = 99): number {
    const lines = this.wrap(font, size, s, maxW).slice(0, maxLines);
    for (let i = 0; i < lines.length; i++) {
      this.text(font, size, x, y + Math.round(size * 0.82) + i * lh, lines[i], c);
    }
    return lines.length * lh;
  }
  // centered wrapped paragraph, returns height used
  paraC(font: TTF, size: number, cx: number, y: number, s: string, maxW: number, lh: number, c: RGB, maxLines = 99): number {
    const lines = this.wrap(font, size, s, maxW).slice(0, maxLines);
    for (let i = 0; i < lines.length; i++) {
      this.text(font, size, cx, y + Math.round(size * 0.82) + i * lh, lines[i], c, "c");
    }
    return lines.length * lh;
  }
}

// ---- scene helpers ----
function skyBand(cv: Canvas, x: number, y: number, w: number, h: number, top: RGB, mid: RGB, bot: RGB): void {
  const third = Math.max(1, Math.floor(h / 3));
  cv.rect(x, y, w, third, top);
  cv.rect(x, y + third, w, h - 2 * third, mid);
  cv.rect(x, y + h - third, w, third, bot);
}
function stars(cv: Canvas, x: number, y: number, w: number, h: number, n: number, seed: number): void {
  const rnd = mulberry32(seed);
  for (let i = 0; i < n; i++) {
    const sx = x + Math.floor(rnd() * w);
    const sy = y + Math.floor(rnd() * h * 0.7);
    const r = rnd() < 0.2 ? 2 : 1;
    cv.circle(sx, sy, r, rnd() < 0.8 ? WHITE : GOLD);
  }
}
function skyline(cv: Canvas, x: number, baseY: number, w: number, h: number, c: RGB, win: RGB, seed: number): void {
  const rnd = mulberry32(seed);
  let cx = x;
  while (cx < x + w - 8) {
    const bw = 14 + Math.floor(rnd() * 26);
    const bh = Math.floor(h * (0.35 + rnd() * 0.65));
    cv.rect(cx, baseY - bh, bw, bh, c);
    for (let wy = baseY - bh + 5; wy < baseY - 4; wy += 7) {
      for (let wx = cx + 3; wx < cx + bw - 3; wx += 6) {
        if (rnd() < 0.4) cv.rect(wx, wy, 2, 3, win);
      }
    }
    cx += bw + 2 + Math.floor(rnd() * 6);
  }
}
function burst(cv: Canvas, cx: number, cy: number, r: number, c: RGB): void {
  for (let k = 0; k < 12; k++) {
    const a = (k / 12) * Math.PI * 2;
    cv.line(cx, cy, Math.round(cx + Math.cos(a) * r), Math.round(cy + Math.sin(a) * r), c, 2);
  }
  cv.circle(cx, cy, Math.max(2, Math.round(r / 4)), c);
}
function dottedArc(cv: Canvas, x0: number, y0: number, x1: number, y1: number, peak: number, c: RGB): void {
  for (let t = 0; t <= 1.0001; t += 0.06) {
    const x = x0 + (x1 - x0) * t;
    const y = y0 + (y1 - y0) * t - Math.sin(t * Math.PI) * peak;
    cv.circle(Math.round(x), Math.round(y), 2, c);
  }
}

// ---- HERO 1: ZELENSKY, big named figure over Kyiv at dusk ----
function heroZelensky(cv: Canvas, x: number, y: number, w: number, h: number): void {
  skyBand(cv, x, y, w, h, [58, 44, 96], [122, 74, 110], [214, 130, 74]);
  stars(cv, x, y, w, h, 26, 11);
  cv.circle(x + w - 42, y + 26, 13, [245, 226, 180]);
  // river + bridge silhouette
  cv.rect(x, y + h - 26, w, 26, [34, 52, 96]);
  cv.poly([[x, y + h - 26], [x + 60, y + h - 58], [x + 130, y + h - 26]], [22, 30, 62]);
  cv.poly([[x + 150, y + h - 26], [x + 210, y + h - 62], [x + 270, y + h - 26]], [22, 30, 62]);
  cv.rect(x, y + h - 28, w, 3, [22, 30, 62]);
  skyline(cv, x, y + h - 26, w, 46, [24, 30, 58], GOLD, 21);
  // figure: head + shoulders, left-centre, large
  const fx = x + 118, fy = y + 78; // face centre
  // shoulders / jacket (olive-green)
  cv.poly([[fx - 78, y + h], [fx - 66, fy + 34], [fx - 30, fy + 18], [fx + 30, fy + 18], [fx + 66, fy + 34], [fx + 78, y + h]], [72, 86, 52]);
  cv.poly([[fx - 30, fy + 18], [fx, fy + 30], [fx + 30, fy + 18], [fx + 22, fy + 44], [fx - 22, fy + 44]], [52, 60, 40]);
  // shirt + collar
  cv.poly([[fx - 14, fy + 20], [fx, fy + 34], [fx + 14, fy + 20], [fx + 10, fy + 30], [fx - 10, fy + 30]], [238, 232, 214]);
  // neck
  cv.rect(fx - 13, fy + 6, 26, 18, SKIN2);
  // head
  cv.ellipse(fx, fy - 12, 30, 36, SKIN);
  // ears
  cv.ellipse(fx - 30, fy - 12, 6, 10, SKIN2);
  cv.ellipse(fx + 30, fy - 12, 6, 10, SKIN2);
  // hair: short, dark, cropped
  cv.poly([[fx - 30, fy - 22], [fx - 28, fy - 44], [fx - 12, fy - 50], [fx + 12, fy - 50], [fx + 28, fy - 44], [fx + 30, fy - 22], [fx + 22, fy - 34], [fx, fy - 38], [fx - 22, fy - 34]], HAIR);
  // stubble on jaw
  cv.ellipse(fx, fy + 8, 24, 18, SKIN2);
  cv.ellipse(fx, fy + 2, 22, 12, SKIN);
  // brows, eyes, nose, mouth
  cv.line(fx - 20, fy - 20, fx - 6, fy - 22, HAIR, 3);
  cv.line(fx + 6, fy - 22, fx + 20, fy - 20, HAIR, 3);
  cv.ellipse(fx - 13, fy - 13, 5, 3, WHITE);
  cv.ellipse(fx + 13, fy - 13, 5, 3, WHITE);
  cv.circle(fx - 13, fy - 13, 2, INK);
  cv.circle(fx + 13, fy - 13, 2, INK);
  cv.line(fx, fy - 10, fx - 2, fy + 2, SKIN2, 2);
  cv.line(fx - 8, fy + 14, fx + 8, fy + 14, [120, 70, 48], 2);
  // microphone (interview)
  cv.line(fx + 52, fy + 62, fx + 34, fy + 30, INK, 3);
  cv.circle(fx + 32, fy + 26, 9, INK);
  cv.circle(fx + 32, fy + 26, 5, [90, 90, 90]);
  // in-scene label
  cv.rect(x + 8, y + 8, 74, 20, WHITE);
  cv.text(sansB, 12, x + 12, y + 22, "KYIV", INK);
  cv.rect(x + w - 96, y + h - 22, 88, 16, RED);
  cv.text(sansB, 10, x + w - 92, y + h - 10, "NBC INTERVIEW", WHITE);
}

// ---- HERO 2: COP31, no deal on day 13 ----
function heroCop31(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [204, 232, 214]);
  // globe
  cv.circle(x + 52, y + 52, 34, [52, 120, 180]);
  cv.ellipse(x + 42, y + 42, 14, 9, GREEN);
  cv.ellipse(x + 64, y + 60, 12, 8, GREEN);
  cv.ellipse(x + 56, y + 36, 7, 5, GREEN);
  cv.ring(x + 52, y + 52, 34, NAVY, 2);
  // thermometer
  cv.rect(x + 118, y + 18, 12, 62, WHITE);
  cv.strokeRect(x + 118, y + 18, 12, 62, INK, 2);
  cv.rect(x + 120, y + 34, 8, 44, RED);
  cv.circle(x + 124, y + 84, 12, RED);
  cv.circle(x + 124, y + 84, 8, REDDK);
  cv.text(sansB, 13, x + 138, y + 34, "+1.5C", RED);
  cv.text(sansB, 9, x + 108, y + 14, "LIMIT AT RISK", RED);
  // clock
  cv.circle(x + 232, y + 48, 30, WHITE);
  cv.ring(x + 232, y + 48, 30, INK, 2);
  cv.line(x + 232, y + 48, x + 232, y + 26, INK, 3);
  cv.line(x + 232, y + 48, x + 248, y + 54, INK, 3);
  cv.circle(x + 232, y + 48, 3, INK);
  cv.rect(x + w - 62, y + 8, 54, 16, WHITE);
  cv.strokeRect(x + w - 62, y + 8, 54, 16, RED, 1);
  cv.text(sansB, 10, x + w - 35, y + 20, "DAY 13", RED, "c");
  // conference table + delegates
  cv.rect(x, y + h - 46, w, 46, [176, 138, 92]);
  cv.rect(x, y + h - 46, w, 4, [120, 88, 50]);
  const suits: RGB[] = [NAVY, [120, 30, 30], [30, 90, 60], [90, 60, 110], [150, 100, 20]];
  for (let i = 0; i < 5; i++) {
    const dx = x + 26 + i * 62;
    cv.poly([[dx - 16, y + h - 46], [dx - 12, y + h - 78], [dx + 12, y + h - 78], [dx + 16, y + h - 46]], suits[i]);
    cv.circle(dx, y + h - 88, 11, SKIN);
    cv.ellipse(dx, y + h - 96, 11, 6, HAIR);
    cv.rect(dx - 10, y + h - 62, 20, 8, WHITE);
  }
  // draft paper on table
  cv.rect(x + w - 92, y + h - 40, 76, 26, WHITE);
  cv.strokeRect(x + w - 92, y + h - 40, 76, 26, INK, 1);
  cv.text(sansB, 9, x + w - 86, y + h - 28, "DRAFT 3", INK);
  cv.text(sans, 7.5, x + w - 86, y + h - 18, "NO FOSSIL FUELS", RED);
  cv.rect(x + 8, y + h - 22, 92, 16, NAVY);
  cv.text(sansB, 10, x + 12, y + h - 10, "AP · AFP", WHITE);
}

// ---- HERO 3: RIYADH, missiles intercepted ----
function heroRiyadh(cv: Canvas, x: number, y: number, w: number, h: number): void {
  skyBand(cv, x, y, w, h, NAVY, [24, 38, 72], [52, 60, 110]);
  stars(cv, x, y, w, h, 30, 13);
  cv.circle(x + w - 36, y + 24, 11, [245, 226, 180]);
  // Kingdom-Centre style tower
  cv.rect(x + 40, y + 40, 26, h - 40, [18, 24, 48]);
  cv.poly([[x + 40, y + 40], [x + 53, y + 62], [x + 66, y + 40]], [18, 24, 48]);
  cv.rect(x + 48, y + 46, 10, 14, SKY);
  skyline(cv, x, y + h, w, 52, [16, 22, 44], GOLD, 23);
  // missile trails + interception bursts
  dottedArc(cv, x + 30, y + h - 8, x + 150, y + 30, 26, GOLD);
  dottedArc(cv, x + 90, y + h - 8, x + 210, y + 22, 30, WHITE);
  dottedArc(cv, x + 170, y + h - 8, x + 260, y + 40, 22, GOLD);
  burst(cv, x + 150, y + 30, 16, [255, 170, 40]);
  burst(cv, x + 210, y + 22, 14, [255, 200, 80]);
  burst(cv, x + 260, y + 40, 12, [255, 170, 40]);
  cv.rect(x + 8, y + 8, 118, 20, RED);
  cv.text(sansB, 12, x + 12, y + 22, "3 SHOT DOWN", WHITE);
  cv.rect(x + w - 118, y + h - 22, 110, 16, [16, 22, 44]);
  cv.text(sansB, 10, x + w - 114, y + h - 10, "COALITION · AFP", WHITE);
}

// ---- MID SCENES (small, each carries a big number/label) ----
function midQuake(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [232, 214, 178]);
  cv.rect(x, y + h - 16, w, 16, [186, 150, 100]);
  cv.poly([[x + 18, y + h - 16], [x + 30, y + h - 38], [x + 42, y + h - 16]], [150, 60, 50]);
  cv.poly([[x + 46, y + h - 16], [x + 58, y + h - 44], [x + 70, y + h - 16]], [150, 60, 50]);
  cv.rect(x + 120, y + h - 30, 46, 14, [120, 90, 60]);
  cv.poly([[x + 120, y + h - 30], [x + 143, y + h - 42], [x + 166, y + h - 30]], [96, 60, 40]);
  cv.line(x + 6, y + 14, x + 30, y + 14, RED, 2);
  cv.line(x + 30, y + 14, x + 38, y + 4, RED, 2);
  cv.line(x + 38, y + 4, x + 48, y + 24, RED, 2);
  cv.line(x + 48, y + 24, x + 56, y + 8, RED, 2);
  cv.line(x + 56, y + 8, x + 70, y + 20, RED, 2);
  cv.line(x + 70, y + 20, x + 84, y + 12, RED, 2);
  cv.text(sansB, 17, x + 96, y + 20, "6.7", RED);
  // bottom-right ground strip: the top-right corner is the house roof, not empty
  cv.text(sans, 8, x + w - 6, y + h - 4, "00:09 UTC", INK, "r");
}
function midDrone(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, SKY);
  cv.rect(x, y + h - 14, w, 14, [40, 110, 170]);
  cv.rect(x, y + h - 14, w, 3, WHITE);
  // drone body
  cv.ellipse(x + 96, y + 20, 34, 7, [70, 78, 88]);
  cv.line(x + 60, y + 20, x + 132, y + 20, [70, 78, 88], 3);
  cv.ellipse(x + 96, y + 12, 8, 5, [90, 98, 110]);
  cv.line(x + 128, y + 16, x + 142, y + 8, [70, 78, 88], 3);
  cv.line(x + 128, y + 24, x + 142, y + 32, [70, 78, 88], 3);
  cv.circle(x + 60, y + 20, 3, RED);
  cv.text(sansB, 15, x + 8, y + 20, "58th", INK);
  cv.text(sans, 8, x + 8, y + 30, "MQ-9 DOWN", RED);
}
function midUranium(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [24, 32, 54]);
  const cx = x + 96, cy = y + 24;
  cv.ellipse(cx, cy, 34, 12, [120, 170, 220]);
  cv.ellipse(cx, cy, 12, 34, [120, 170, 220]);
  cv.circle(cx, cy, 7, GOLD);
  cv.ring(cx, cy, 34, [200, 210, 230], 1);
  cv.text(sansB, 13, x + 8, y + 20, "U", WHITE);
  cv.text(sans, 9, x + 8, y + 32, "STAYS", GOLD);
  cv.text(sans, 8, x + 150, y + 42, "TEHRAN", WHITE);
}
function midAiTax(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, NAVY2);
  cv.rect(x + 118, y + 8, 34, 34, GOLD);
  cv.strokeRect(x + 118, y + 8, 34, 34, [140, 100, 10], 2);
  for (let i = 0; i < 4; i++) {
    cv.rect(x + 122 + i * 8, y + 4, 3, 4, GOLD);
    cv.rect(x + 122 + i * 8, y + 42, 3, 4, GOLD);
  }
  cv.text(sansB, 12, x + 124, y + 30, "AI", NAVY);
  cv.text(sansB, 20, x + 10, y + 30, "%", WHITE);
  cv.text(sans, 9, x + 10, y + 42, "TAX ABROAD", GOLD);
}
function midFlags(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, CREAM);
  // China flag (shrunk so the label below sits on plain cream, not on the flag)
  cv.rect(x + 14, y + 8, 62, 22, RED);
  cv.circle(x + 26, y + 17, 5, GOLD);
  for (let i = 0; i < 4; i++) cv.circle(x + 44 + (i % 2) * 12, y + 12 + Math.floor(i / 2) * 9, 2, GOLD);
  // Japan flag
  cv.rect(x + 110, y + 8, 62, 22, WHITE);
  cv.strokeRect(x + 110, y + 8, 62, 22, GREY, 1);
  cv.circle(x + 141, y + 19, 9, RED);
  cv.text(sansB, 10, x + 14, y + 42, "BEIJING  ·  TOKYO", INK);
}
function midPlane(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [168, 206, 232]);
  cv.ellipse(x + 40, y + 12, 16, 6, WHITE);
  cv.ellipse(x + 120, y + 20, 22, 7, WHITE);
  cv.rect(x, y + h - 12, w, 12, [90, 96, 104]);
  cv.rect(x, y + h - 12, w, 2, WHITE);
  // plane
  cv.ellipse(x + 96, y + 30, 44, 7, WHITE);
  cv.poly([[x + 52, y + 30], [x + 78, y + 18], [x + 96, y + 26]], WHITE);
  cv.poly([[x + 118, y + 28], [x + 140, y + 38], [x + 128, y + 30]], WHITE);
  cv.line(x + 138, y + 28, x + 150, y + 20, WHITE, 4);
  cv.text(sansB, 15, x + 8, y + 16, "146", INK);
  cv.text(sansB, 9, x + 8, y + 28, "SAFE", RED);
}
function midAiTalks(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [226, 240, 226]);
  cv.ellipse(x + 52, y + 15, 34, 14, [40, 120, 80]);
  cv.poly([[x + 34, y + 25], [x + 40, y + 31], [x + 46, y + 25]], [40, 120, 80]);
  cv.text(sansB, 10, x + 30, y + 19, "AI ?", WHITE);
  cv.ellipse(x + 140, y + 15, 34, 14, GOLD);
  cv.poly([[x + 158, y + 25], [x + 152, y + 31], [x + 146, y + 25]], GOLD);
  cv.text(sansB, 10, x + 122, y + 19, "LET'S", NAVY);
  cv.text(sans, 9, x + 60, y + 42, "CANBERRA · 11 DAYS", INK);
}
function midBitcoin(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [22, 26, 38]);
  cv.circle(x + 150, y + 24, 16, [240, 140, 40]);
  cv.text(sansB, 16, x + 143, y + 30, "B", WHITE);
  cv.line(x + 10, y + 8, x + 40, y + 14, RED, 2);
  cv.line(x + 40, y + 14, x + 62, y + 11, RED, 2);
  cv.line(x + 62, y + 11, x + 92, y + 24, RED, 2);
  cv.line(x + 92, y + 24, x + 118, y + 20, RED, 2);
  // solid chip for the numbers, clear of the chart lines
  cv.rect(x + 6, y + 30, 122, 13, [48, 54, 72]);
  cv.text(sansB, 13, x + 10, y + 41, "$58,983", WHITE);
  cv.text(sans, 8, x + 96, y + 41, "-3.9%", [255, 150, 140]);
}
function midF1(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [40, 44, 52]);
  cv.rect(x, y + 22, w, 16, [70, 76, 84]);
  for (let dx = 0; dx < w; dx += 16) cv.rect(x + dx, y + 29, 8, 2, WHITE);
  // F1 car
  cv.rect(x + 62, y + 14, 66, 8, RED);
  cv.poly([[x + 128, y + 14], [x + 142, y + 20], [x + 128, y + 22]], RED);
  cv.poly([[x + 62, y + 14], [x + 74, y + 6], [x + 88, y + 14]], RED);
  cv.circle(x + 76, y + 24, 7, INK);
  cv.circle(x + 76, y + 24, 3, GREY);
  cv.circle(x + 118, y + 24, 7, INK);
  cv.circle(x + 118, y + 24, 3, GREY);
  cv.text(sansB, 15, x + 8, y + 16, "P1", WHITE);
  // solid chip for the time, clear of the road and its dashes
  cv.rect(x + 138, y + 32, 54, 12, [18, 20, 28]);
  cv.text(sans, 8, x + 144, y + 42, "1:34.041", GOLD);
}
function midCricket(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [58, 140, 72]);
  cv.rect(x, y + h - 12, w, 12, [46, 110, 58]);
  // stumps
  cv.rect(x + 150, y + 18, 3, 16, GOLD);
  cv.rect(x + 156, y + 18, 3, 16, GOLD);
  cv.rect(x + 162, y + 18, 3, 16, GOLD);
  // bat + ball
  cv.line(x + 40, y + 40, x + 78, y + 10, [210, 170, 110], 5);
  cv.circle(x + 88, y + 8, 5, RED);
  cv.circle(x + 88, y + 8, 2, WHITE);
  cv.text(sansB, 17, x + 8, y + 20, "124*", WHITE);
  cv.text(sans, 8, x + 8, y + 32, "AT TEA", GOLD);
}

// ---- world map ----
type LonLat = [number, number];
const CONTINENTS: LonLat[][] = [
  // North America
  [[-168,66],[-140,70],[-125,71],[-110,68],[-95,69],[-85,66],[-80,73],[-70,62],[-65,60],[-55,52],[-60,47],[-70,44],[-75,39],[-80,32],[-81,26],[-90,21],[-97,16],[-94,17],[-87,13],[-83,9],[-79,9],[-92,15],[-105,20],[-110,24],[-114,29],[-120,34],[-125,40],[-124,48],[-135,58],[-150,60],[-165,60]],
  // Greenland
  [[-58,64],[-52,70],[-40,76],[-25,76],[-20,70],[-30,65],[-45,60]],
  // South America
  [[-79,9],[-77,4],[-80,-3],[-81,-6],[-77,-12],[-72,-18],[-70,-23],[-70,-33],[-72,-42],[-74,-52],[-70,-55],[-66,-55],[-68,-50],[-62,-41],[-57,-38],[-52,-33],[-48,-28],[-41,-23],[-35,-9],[-44,-3],[-50,0],[-55,5],[-62,8],[-70,11]],
  // Africa
  [[-17,15],[-17,21],[-10,31],[-5,35],[10,37],[11,34],[20,32],[30,31],[32,31],[35,28],[38,22],[40,15],[43,11],[51,12],[48,5],[42,-1],[40,-10],[36,-18],[33,-26],[28,-33],[20,-35],[17,-32],[14,-22],[12,-12],[9,-1],[9,4],[-8,5],[-13,8],[-17,12]],
  // Eurasia
  [[-10,36],[-9,43],[-2,48],[0,51],[5,53],[8,57],[10,59],[18,56],[21,55],[24,59],[30,62],[32,70],[40,68],[50,69],[60,69],[70,72],[80,73],[90,75],[100,77],[110,74],[120,73],[130,72],[140,72],[150,70],[160,69],[170,66],[178,65],[170,60],[162,56],[158,52],[150,59],[142,55],[140,45],[135,43],[130,38],[127,35],[122,38],[120,32],[115,23],[110,20],[108,18],[105,10],[103,8],[100,8],[98,12],[95,16],[92,21],[89,22],[86,20],[80,13],[77,8],[75,12],[72,20],[68,23],[66,25],[62,25],[58,26],[56,27],[52,28],[50,30],[48,30],[44,29],[40,31],[36,36],[33,36],[30,36],[27,37],[26,38],[23,36],[22,37],[19,40],[15,44],[12,44],[8,44],[3,43],[-2,37],[-6,36],[-10,36]],
  // Australia
  [[114,-22],[114,-30],[115,-34],[120,-34],[124,-33],[129,-32],[132,-32],[135,-35],[138,-35],[140,-38],[145,-38],[150,-37],[153,-32],[153,-27],[150,-23],[146,-19],[142,-15],[142,-11],[137,-12],[135,-15],[132,-12],[130,-13],[126,-14],[122,-17],[118,-20]],
  // UK
  [[-5,50],[-3,53],[-5,56],[-3,58],[-1,57],[0,53],[1,51]],
  // Japan
  [[130,31],[132,33],[135,34],[137,35],[139,36],[140,38],[141,41],[143,43],[141,45],[140,40],[139,37],[137,35],[133,34],[131,32]],
  // Sumatra
  [[95,5],[100,0],[104,-3],[106,-6],[103,-5],[98,-1],[95,2]],
  // Borneo
  [[109,1],[113,4],[117,2],[118,-3],[115,-4],[111,-3],[109,-1]],
  // New Guinea
  [[131,-1],[136,-2],[141,-3],[146,-6],[150,-8],[147,-9],[141,-8],[136,-6],[132,-4]],
  // New Zealand
  [[167,-45],[170,-42],[173,-40],[175,-38],[177,-38],[174,-41],[171,-44],[168,-46]],
];
const PINS: [number, number, number][] = [
  [1, 30.5, 50.4], [2, 30.7, 36.9], [3, 46.7, 24.7], [4, -75.9, -11.2],
  [5, 56.5, 27.0], [6, 51.4, 35.7], [7, -77.0, 38.9], [8, 116.4, 39.9],
  [9, 125.6, 7.1], [10, 149.1, -35.3], [11, -0.1, 51.5], [12, -115.1, 36.2],
  [13, 174.8, -41.3],
];

function drawMap(cv: Canvas, x: number, y: number, w: number, h: number): void {
  cv.rect(x, y, w, h, [207, 227, 238]);
  cv.strokeRect(x, y, w, h, INK, 1);
  const proj = (lon: number, lat: number): [number, number] => [
    x + ((lon + 170) / 360) * w,
    y + ((75 - lat) / 130) * h,
  ];
  for (const cont of CONTINENTS) {
    cv.poly(cont.map(([lo, la]) => proj(lo, la)), [227, 211, 168]);
  }
  // pin numbers
  for (const [n, lo, la] of PINS) {
    const [px, py] = proj(lo, la);
    cv.circle(px, py, 8, RED);
    cv.ring(px, py, 8, WHITE, 1);
    cv.text(sansB, 9, px, py + 3, String(n), WHITE, "c");
  }
}

// ---- content ----
const STATS: [string, string][] = [
  ["13", "day of COP31"],
  ["3", "missiles downed over Riyadh"],
  ["6.7", "magnitude of the Peru quake"],
  ["146", "safe in Davao"],
  ["$58,983", "bitcoin, down 3.9%"],
  ["124*", "Rahul at tea, Wellington"],
];
const REGIONS: [string, RGB, number][] = [
  ["EUROPE 4", BLUE, 130], ["ASIA 10", RED, 200], ["MIDDLE EAST 5", ORANGE, 140],
  ["AFRICA 1", PURPLE, 95], ["AMERICAS 11", GREEN, 200], ["OCEANIA 3", TEAL, 130],
  ["GLOBAL 1", GREY, 101],
];
interface Mid { n: number; banner: string; kicker: string; head: string; deck: string; scene: (cv: Canvas, x: number, y: number, w: number, h: number) => void; }
const MIDS: Mid[] = [
  { n: 4, banner: "PERU: QUAKE 6.7", kicker: "JUNIN, PERU · EARTHQUAKE", head: "Magnitude 6.7 earthquake shakes central Peru", deck: "Felt in Lima and along the coast. No deaths or tsunami risk. (USGS, IGP)", scene: midQuake },
  { n: 5, banner: "HORMUZ: DRONE", kicker: "STRAIT OF HORMUZ · WAR", head: "Iran says it downed a US drone", deck: "IRGC claims it shot down a US MQ-9, the 58th. No US confirmation. (IRIB)", scene: midDrone },
  { n: 6, banner: "IRAN: URANIUM", kicker: "TEHRAN · DIPLOMACY", head: "Iran: uranium stock stays at home", deck: "Minister still seeks a \"fair solution\". (ToI)", scene: midUranium },
  { n: 7, banner: "TRUMP: AI TAX", kicker: "WASHINGTON · TECHNOLOGY", head: "Trump vows tax on data centres abroad", deck: "\"Tremendous\" penalty promised, no details yet. (ABC)", scene: midAiTax },
  { n: 8, banner: "CHINA–JAPAN", kicker: "BEIJING · DIPLOMACY", head: "China tells Japan to 'correct' Taiwan words", deck: "Tokyo says its stance is unchanged. (Ministry, AFP)", scene: midFlags },
  { n: 9, banner: "DAVAO: 146 SAFE", kicker: "DAVAO · AVIATION", head: "Jet lands safely after engine fire alert", deck: "Air Niugini 767 diverts after midnight; all 146 safe. (Airline, AP)", scene: midPlane },
  { n: 10, banner: "CANBERRA: AI", kicker: "CANBERRA · DIPLOMACY", head: "Australia and China agree to AI talks", deck: "Albanese ends an 11-day trip. (ABC)", scene: midAiTalks },
  { n: 11, banner: "BITCOIN: $58,983", kicker: "WORLD · MARKETS", head: "Bitcoin slips below $59,000", deck: "Down 3.9% in 24 hours. (CoinGecko)", scene: midBitcoin },
  { n: 12, banner: "RUSSELL: P1", kicker: "LAS VEGAS · FORMULA ONE", head: "Russell fastest in final Las Vegas practice", deck: "1:34.041 in a damp, messy session. (Formula 1)", scene: midF1 },
  { n: 13, banner: "RAHUL: 124*", kicker: "WELLINGTON · CRICKET", head: "Rahul century puts India on top", deck: "India 344 for 2 at tea, replying to 368. (AFP)", scene: midCricket },
];
const ALSO: string[] = [
  "Kryvyi Rih: Double strike kills 2, injures 42 (Kyiv Ind.)",
  "Copenhagen: Russian attack plot expelled (Al Jazeera)",
  "Antalya: EU warns COP31 risks a \"fossil summit\" (AFP)",
  "Antalya: Panama threatens to block climate deal (Al Jazeera)",
  "Antalya: Indonesia's PLN signs clean-power deals (Antara)",
  "Yemen: Houthis threaten Jeddah and Red Sea ports (Al Jazeera)",
  "Washington: Vance — Iran strikes were Trump's decision (Reuters)",
  "Washington: Lawmaker threatens SpaceX's funding (CNN)",
  "Texas: Execution of a man of 70 takes 63 minutes (ABC)",
  "Los Angeles: Jury convicts man of starting Palisades fire (ABC)",
  "Missouri: Judge approves $7.25bn Roundup settlement (AFP)",
  "Vancouver: Canada rests defence in youth climate trial (AFP)",
  "Pyongyang: Kim tours factories (AFP)",
  "Sejong: Freight train derails, no one hurt (Korea Herald)",
  "Taipei: Budget and cash payout passed (Taipei Times)",
  "Bangkok: Six-point plan on arsenic in two rivers (The Nation)",
  "New Delhi: Pakistani minister joins SCO forum in India (Dawn)",
  "Eastern India: Rain alerts as Akvan's remnants move inland (ETV)",
  "Myanmar: Rights groups urge sanctions after court ruling (AP)",
  "Port Louis: African rating agency talks to 15 states (Al Jazeera)",
  "Melbourne: Cummins keeps the Australian captaincy (ABC)",
  "Las Vegas: Verstappen sent to stewards after contact (Autosport)",
];
const DATECHECK = "Left out as Friday 20 November's news: Wall Street's fall into correction · the Russian barrage on Kyiv's bridges · the missile that landed in Poland · the UK–EU deal · Cyclone Akvan's landfall. Older still: the Trump–Xi–Putin Shenzhen summit (Thu 19 Nov) · the ICJ Myanmar genocide ruling (Fri 20 Nov) · Anthropic's debut (Thu 19 Nov) · GTA VI's launch (Thu 19 Nov) · Voyager 1's light-day (18 Nov). Not confirmed when drawn, so not shown: BepiColombo entering Mercury orbit · a final COP31 text.";

// ---- layout ----
function build(): Canvas {
  const cv = new Canvas();
  cv.grain(0, 0, W, H, 1, 7);
  const MX = 14, CW = 996, RX = MX + CW;

  // kicker
  cv.text(sansB, 12, MX, 22, "THE WORLD IN ONE DAY", RED);
  cv.text(sansB, 11, RX, 22, "35 STORIES · 7 REGIONS · EVERY ONE DATED SATURDAY 21 NOVEMBER 2026", INK, "r");
  cv.hline(MX, 28, CW, INK);
  // masthead
  cv.text(serifB, 60, MX, 86, "Saturday 21 November 2026", INK);
  cv.text(serif, 15, 512, 106, "Zelensky warns Crimea bridge 'will not stay' · COP31 runs past its deadline · Three missiles downed over Riyadh", INK, "c", 0.18);
  cv.hline(MX, 112, CW, INK);

  // stat strip: 6 cells
  const sw = CW / 6;
  for (let i = 0; i < 6; i++) {
    const cx0 = MX + i * sw;
    if (i > 0) cv.vline(Math.round(cx0), 118, 34, INK);
    cv.text(sansB, 28, cx0 + 10, 142, STATS[i][0], RED);
    const cap = cv.wrap(sans, 9, STATS[i][1], sw - 20);
    for (let l = 0; l < Math.min(2, cap.length); l++) {
      cv.text(sans, 9, cx0 + 10, 154 + l * 11, cap[l], INK);
    }
  }
  // region strip
  let rx = MX;
  for (const [label, col, w] of REGIONS) {
    cv.rect(rx, 168, w, 16, col);
    cv.text(sansB, 10, rx + w / 2, 180, label, WHITE, "c");
    rx += w;
  }

  // heroes
  const heroW = 326, heroGap = 9;
  const heroes = [
    { n: 1, banner: "KYIV: ZELENSKY WARNS", kicker: "KYIV · WAR", head: "Zelensky: Crimea bridge 'will not stay'", deck: "He warns of double-tap strikes in an NBC interview. (NBC)", scene: heroZelensky },
    { n: 2, banner: "COP31: OVERTIME", kicker: "ANTALYA, TURKIYE · CLIMATE", head: "Climate talks miss their deadline", deck: "Nearly 200 nations fail to agree by Friday's 6pm close; a draft with no mention of fossil fuels split the summit. A third text is due on Saturday morning. (AP, AFP)", scene: heroCop31 },
    { n: 3, banner: "RIYADH: MISSILES", kicker: "RIYADH, SAUDI ARABIA · WAR", head: "Three Houthi missiles shot down over Riyadh", deck: "Saudi air defences destroyed three ballistic missiles aimed at the capital around 2am, the third straight night of alerts. No damage or casualties were reported. (Reuters, AFP)", scene: heroRiyadh },
  ];
  const hy = 190, hScene = 138;
  for (let i = 0; i < 3; i++) {
    const hx = MX + i * (heroW + heroGap);
    const hh = heroes[i];
    hh.scene(cv, hx, hy, heroW, hScene);
    cv.strokeRect(hx, hy, heroW, hScene, INK, 1);
    cv.rect(hx, hy + hScene, heroW, 20, RED);
    cv.text(sansB, 12, hx + 8, hy + hScene + 14, hh.banner, WHITE);
    cv.text(sansB, 10, hx, hy + hScene + 34, hh.n + "  " + hh.kicker, RED);
    const hl = cv.wrap(sansB, 20, hh.head, heroW);
    const headLines = Math.min(2, hl.length);
    for (let l = 0; l < headLines; l++) {
      cv.text(sansB, 20, hx, hy + hScene + 58 + l * 23, hl[l], INK);
    }
    // deck starts after the wrapped headline + a fixed gap (never touching)
    const deckY = hy + hScene + 84 + (headLines - 1) * 4;
    cv.para(sans, 10, hx, deckY, hh.deck, heroW, 12.5, INK, 3);
  }
  const heroEnd = hy + hScene + 122; // banner 20 + kicker 14 + headline 46 + 3 deck lines

  // mid stories: 5 cols x 2 rows
  const midW = 196, midGap = 4, midH = 130;
  for (let r = 0; r < 2; r++) {
    for (let c = 0; c < 5; c++) {
      const m = MIDS[r * 5 + c];
      const mx = MX + c * (midW + midGap);
      const my = heroEnd + 10 + r * (midH + 6);
      m.scene(cv, mx, my, midW, 44);
      cv.strokeRect(mx, my, midW, 44, INK, 1);
      cv.rect(mx, my + 44, midW, 15, RED);
      cv.text(sansB, 10, mx + 5, my + 44 + 11, m.banner, WHITE);
      cv.text(sansB, 9, mx, my + 71, m.n + "  " + m.kicker, RED);
      const hl = cv.wrap(sansB, 12.5, m.head, midW);
      const headLines = Math.min(2, hl.length);
      for (let l = 0; l < headLines; l++) {
        cv.text(sansB, 12.5, mx, my + 86 + l * 14.5, hl[l], INK);
      }
      // deck starts after the wrapped headline + a fixed gap (never touching)
      const deckY = my + 100 + (headLines - 1) * 8;
      cv.para(sans, 9.5, mx, deckY, m.deck, midW, 12, INK, 2);
    }
  }
  const midEnd = heroEnd + 10 + 2 * midH + 6;

  // map + also-on
  const mapY = midEnd + 8;
  cv.text(sansB, 11, MX, mapY + 11, "WHERE IT HAPPENED", INK);
  drawMap(cv, MX, mapY + 16, 330, 148);
  const alsoX = 360, alsoW = 650;
  cv.text(sansB, 12, alsoX, mapY + 11, "ALSO ON SATURDAY 21 NOVEMBER 2026 — 22 MORE STORIES", RED);
  const alsoH = 148;
  const colW = 318;
  const cols: string[][] = [ALSO.slice(0, 11), ALSO.slice(11)];
  for (const fs of [9.5, 9, 8.5]) {
    let ok = true;
    const laid: string[][][] = [[], []];
    for (let ci = 0; ci < 2; ci++) {
      for (let i = 0; i < cols[ci].length; i++) {
        const n = 14 + ci * 11 + i;
        const lines = cv.wrap(sans, fs, n + "  " + cols[ci][i], colW);
        if (lines.length > 2) { ok = false; break; }
        laid[ci].push(lines);
      }
      if (!ok) break;
    }
    if (!ok) continue;
    const lh = Math.round(fs * 1.55);
    const total = Math.max(laid[0].length, laid[1].length);
    let need = 0;
    for (let ci = 0; ci < 2; ci++) {
      let h = 0;
      for (const lines of laid[ci]) h += lines.length * lh;
      need = Math.max(need, h);
    }
    if (need > alsoH) continue;
    for (let ci = 0; ci < 2; ci++) {
      const cx0 = alsoX + ci * (colW + 14);
      let yy = mapY + 16;
      for (const lines of laid[ci]) {
        for (let l = 0; l < lines.length; l++) {
          cv.text(sans, fs, cx0, yy + Math.round(fs * 0.82) + l * lh, lines[l], INK);
        }
        yy += lines.length * lh;
      }
    }
    break;
  }

  // date check
  const dcY = mapY + 172;
  cv.strokeRect(MX, dcY, CW, 76, RED, 2);
  cv.text(sansB, 12, MX + 8, dcY + 16, "DATE CHECK", RED);
  cv.para(sans, 10.5, MX + 8, dcY + 22, DATECHECK, CW - 16, 15, INK, 4);
  // footer
  cv.text(sans, 10, 512, dcY + 92, "Every story here happened, or was first reported, on Saturday 21 November 2026. Sources named beside each story · Original drawings", GREY, "c");
  return cv;
}

function main(): void {
  const cv = build();
  const png = encodePNG(W, H, cv.buf);
  fs.mkdirSync(OUT, { recursive: true });
  fs.writeFileSync(path.join(OUT, "entry.png"), png);
  console.log("wrote " + path.join(OUT, "entry.png") + " (" + png.length + " bytes)");
}

main();
