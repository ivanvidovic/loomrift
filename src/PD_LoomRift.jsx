import React, { useState, useMemo, useRef, useCallback, useEffect, useReducer, useDeferredValue } from "react";

/* ============================================================
   PD_LoomRift v1.5
   Procedural gradient-tile collage generator -> SVG / PNG
   ============================================================ */

/* ---------------- rng / weights ---------------- */
function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const pick = (arr, r) => arr[Math.floor(r() * arr.length) % arr.length];
const rint = (r, a, b) => a + Math.floor(r() * (b - a + 1));
const rflt = (r, a, b) => a + r() * (b - a);

function makeWeights(n, mode, r) {
  n = Math.max(1, n | 0);
  if (mode === "even") return Array(n).fill(1);
  if (mode === "random") return Array.from({ length: n }, () => 0.3 + r() * 1.9);
  if (mode === "fib") {
    const f = [1, 1];
    while (f.length < n) f.push(f[f.length - 1] + f[f.length - 2]);
    const s = f.slice(0, n);
    for (let i = s.length - 1; i > 0; i--) { const j = Math.floor(r() * (i + 1)); [s[i], s[j]] = [s[j], s[i]]; }
    return s;
  }
  let w = [1], guard = 0;
  while (w.length < n && guard++ < 500) { const i = Math.floor(r() * w.length); const v = w[i] / 2; w.splice(i, 1, v, v); }
  return w.slice(0, n);
}
const toOffsets = (w, total) => {
  const sum = w.reduce((a, b) => a + b, 0);
  let acc = 0;
  return w.map((v) => { const o = { pos: (acc / sum) * total, size: (v / sum) * total }; acc += v; return o; });
};

/* ---------------- gradients ---------------- */
const RAMPS = ["linear", "gamma", "triangle", "steps", "sine"];
const DIRS = { r: [0, 0, 1, 0], l: [1, 0, 0, 0], d: [0, 0, 0, 1], u: [0, 1, 0, 0] };

function rampStops(ramp, p, invert) {
  const f = (v) => (invert ? 1 - v : v);
  const hex = (v) => {
    const c = Math.max(0, Math.min(255, Math.round(v * 255)));
    const h = c.toString(16).padStart(2, "0");
    return `#${h}${h}${h}`;
  };
  let pts = [];
  if (ramp === "linear") pts = [[0, 0], [1, 1]];
  else if (ramp === "gamma") { const g = Math.max(0.15, p); for (let i = 0; i <= 10; i++) pts.push([i / 10, Math.pow(i / 10, g)]); }
  else if (ramp === "triangle") pts = [[0, 0], [0.5, 1], [1, 0]];
  else if (ramp === "sine") { for (let i = 0; i <= 12; i++) pts.push([i / 12, (1 - Math.cos(Math.PI * (i / 12))) / 2]); }
  else { const n = Math.max(2, Math.round(p)); for (let i = 0; i < n; i++) { const v = i / (n - 1); pts.push([i / n, v], [(i + 1) / n, v]); } }
  return pts.map(([o, v]) => `<stop offset="${+o.toFixed(4)}" stop-color="${hex(f(v))}"/>`).join("");
}

class GradReg {
  constructor() { this.map = new Map(); }
  id(ramp, p, dir, invert) {
    const key = `${ramp}|${+p.toFixed(2)}|${dir}|${invert ? 1 : 0}`;
    if (!this.map.has(key)) this.map.set(key, { id: `pdg${this.map.size}`, ramp, p, dir, invert });
    return this.map.get(key).id;
  }
  defs() {
    return [...this.map.values()].map((g) => {
      const [x1, y1, x2, y2] = DIRS[g.dir];
      return `<linearGradient id="${g.id}" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}">${rampStops(g.ramp, g.p, g.invert)}</linearGradient>`;
    }).join("");
  }
}

/* ---------------- tile geometry ---------------- */
const U = 1000;
const GEN_KEYS = ["seed", "cols", "rows", "colMode", "rowMode", "stripeMode", "freqMin", "freqMax",
  "freqMapX", "freqMapY", "axisBias", "invertChance", "voidChance", "rampMode", "gamma", "stepMax", "pingPong"];
const genParams = (L) => Object.fromEntries(GEN_KEYS.map((k) => [k, L[k]]));

function buildTile(P, reg) {
  const r = mulberry32(P.seed >>> 0);
  const cols = toOffsets(makeWeights(P.cols, P.colMode, r), U);
  const rows = toOffsets(makeWeights(P.rows, P.rowMode, r), U);
  const out = [];
  rows.forEach((ro, ri) => {
    cols.forEach((co, ci) => {
      if (r() < P.voidChance) return;
      const nx = cols.length > 1 ? ci / (cols.length - 1) : 0;
      const ny = rows.length > 1 ? ri / (rows.length - 1) : 0;
      const bias = Math.max(0, Math.min(1, r() + P.freqMapX * (nx - 0.5) * 2 + P.freqMapY * (ny - 0.5) * 2));
      const freq = Math.max(1, Math.round(P.freqMin + bias * (P.freqMax - P.freqMin)));
      const axis = r() < P.axisBias ? "x" : "y";
      const baseFlip = r() < 0.5;
      const cellInvert = r() < P.invertChance;
      const ramp = P.rampMode === "mixed" ? pick(RAMPS, r) : P.rampMode;
      const p = ramp === "steps" ? 2 + Math.round(r() * (P.stepMax - 2)) : P.gamma;
      const sw = toOffsets(makeWeights(freq, P.stripeMode, r), axis === "x" ? co.size : ro.size);
      sw.forEach((s, si) => {
        const flip = P.pingPong ? (baseFlip !== (si % 2 === 1)) : baseFlip;
        const dir = axis === "x" ? (flip ? "l" : "r") : (flip ? "u" : "d");
        const gid = reg.id(ramp, p, dir, cellInvert);
        const x = axis === "x" ? co.pos + s.pos : co.pos;
        const y = axis === "x" ? ro.pos : ro.pos + s.pos;
        const w = axis === "x" ? s.size : co.size;
        const h = axis === "x" ? ro.size : s.size;
        out.push(`<rect x="${+x.toFixed(2)}" y="${+y.toFixed(2)}" width="${+(w + 0.4).toFixed(2)}" height="${+(h + 0.4).toFixed(2)}" fill="url(#${gid})"/>`);
      });
    });
  });
  return out.join("");
}

/* geometry cache: one <g> per unique parameter set, referenced by <use> */
class TileBank {
  constructor(reg) { this.reg = reg; this.map = new Map(); }
  ref(P) {
    const k = GEN_KEYS.map((x) => P[x]).join("|");
    if (!this.map.has(k)) this.map.set(k, { id: `pdt${this.map.size}`, markup: buildTile(P, this.reg) });
    return this.map.get(k);
  }
  defs() { return [...this.map.values()].map((t) => `<g id="${t.id}">${t.markup}</g>`).join(""); }
}

/* ---------------- packing ---------------- */
/* uniform repeat grid */
function repeatCells(L, r) {
  const cw = toOffsets(makeWeights(Math.max(1, L.tileX | 0), L.tileMode, r), U);
  const ch = toOffsets(makeWeights(Math.max(1, L.tileY | 0), L.tileMode, r), U);
  const out = [];
  ch.forEach((rr) => cw.forEach((cc) => out.push({ x: cc.pos, y: rr.pos, w: cc.size, h: rr.size })));
  return out;
}

/* recursive binary split — always fills the box exactly, cell ratios vary */
function collageCells(L, r) {
  let cells = [{ x: 0, y: 0, w: U, h: U }];
  const n = Math.max(1, L.cells | 0);
  let guard = 0;
  while (cells.length < n && guard++ < 600) {
    const sorted = [...cells].sort((a, b) => b.w * b.h - a.w * a.h);
    const idx = Math.min(sorted.length - 1, Math.floor(Math.pow(r(), 1 + L.evenness * 5) * sorted.length));
    const t = sorted[idx];
    const i = cells.indexOf(t);
    const horiz = L.splitAxis === "auto" ? t.w >= t.h : r() < 0.5;
    const f = Math.max(0.08, Math.min(0.92, 0.5 + (r() - 0.5) * L.aspectVar * 0.85));
    const a = horiz ? { x: t.x, y: t.y, w: t.w * f, h: t.h } : { x: t.x, y: t.y, w: t.w, h: t.h * f };
    const b = horiz ? { x: t.x + t.w * f, y: t.y, w: t.w * (1 - f), h: t.h }
      : { x: t.x, y: t.y + t.h * f, w: t.w, h: t.h * (1 - f) };
    cells.splice(i, 1, a, b);
  }
  return cells;
}

function layerContent(L, bank, tiles, expand) {
  const r = mulberry32((L.seed ^ 0x9e3779b9) >>> 0);
  const collage = L.mode === "collage";
  const cells = collage ? collageCells(L, r) : repeatCells(L, r);

  const pool = collage
    ? (tiles.filter((t) => t.on).map((t) => t.params).concat(tiles.some((t) => t.on) ? [] : [genParams(L)]))
    : [genParams(L)];

  const gap = collage ? L.gap : 0;
  const parts = [];
  cells.forEach((c) => {
    const P = pool.length === 1 ? pool[0] : pick(pool, r);
    const t = bank.ref(P);
    const rotate = collage ? (r() < L.rotChance ? pick([90, 180, 270], r) : 0)
      : (L.tileRot ? pick([0, 90, 180, 270], r) : 0);
    const doFlip = collage ? r() < L.flipChance : L.tileFlip && r() < 0.5;
    const fx = doFlip ? -1 : 1;
    const fy = (collage ? r() < L.flipChance : L.tileFlip && r() < 0.5) ? -1 : 1;
    const w = Math.max(1, c.w - gap), h = Math.max(1, c.h - gap);
    const tr = `translate(${(c.x + c.w / 2).toFixed(2)} ${(c.y + c.h / 2).toFixed(2)}) ` +
      `scale(${(fx * w / U).toFixed(5)} ${(fy * h / U).toFixed(5)}) rotate(${rotate}) translate(${-U / 2} ${-U / 2})`;
    parts.push(expand ? `<g transform="${tr}">${t.markup}</g>` : `<g transform="${tr}"><use href="#${t.id}"/></g>`);
  });
  return parts.join("");
}

/* Layers live in a square master the size of the canvas's longer edge, centred.
   1:1 shows all of it; every other ratio is a crop of the same artwork, so
   switching aspect never restretches the design. */
function layerTransform(L, W, H) {
  const M = Math.max(W, H);
  const ox = (W - M) / 2, oy = (H - M) / 2;
  const bx = ox + (L.x / 100) * M, by = oy + (L.y / 100) * M;
  const bw = (L.w / 100) * M, bh = (L.h / 100) * M;
  return [
    `translate(${(bx + bw / 2).toFixed(2)} ${(by + bh / 2).toFixed(2)})`,
    L.rot ? `rotate(${L.rot})` : "",
    L.skew ? `skewX(${L.skew})` : "",
    `scale(${((L.flipX ? -1 : 1) * bw / U).toFixed(5)} ${((L.flipY ? -1 : 1) * bh / U).toFixed(5)})`,
    `translate(${-U / 2} ${-U / 2})`,
  ].filter(Boolean).join(" ");
}

function buildSVG(doc, expand = false) {
  const { W, H, layers, bg, tiles } = doc;
  const reg = new GradReg();
  const bank = new TileBank(reg);
  const built = layers.map((L) => ({ L, content: L.visible ? layerContent(L, bank, tiles, expand) : "" }));

  const masks = [], body = [];
  built.forEach((b, i) => {
    const { L } = b;
    if (!L.visible) return;
    const g = `<g transform="${layerTransform(L, W, H)}">${b.content}</g>`;
    if (L.role === "mask") {
      const mid = `m_${L.id}`;
      masks.push(`<mask id="${mid}" maskUnits="userSpaceOnUse" x="0" y="0" width="${W}" height="${H}" style="mask-type:luminance"><rect x="0" y="0" width="${W}" height="${H}" fill="${L.maskInvert ? "#fff" : "#000"}"/><g${L.maskInvert ? ' style="mix-blend-mode:difference"' : ""}>${g}</g></mask>`);
      for (let j = i - 1; j >= 0; j--) if (built[j].L.visible && built[j].L.role === "paint") { built[j].maskId = mid; break; }
      return;
    }
    b.paint = g;
  });
  built.forEach((b) => {
    if (!b.paint) return;
    const { L } = b;
    const m = b.maskId ? ` mask="url(#${b.maskId})"` : "";
    body.push(`<g id="${L.name.replace(/[^\w-]/g, "_")}" style="mix-blend-mode:${L.blend};opacity:${L.opacity}"${m}>${b.paint}</g>`);
  });

  return `<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}">` +
    `<defs>${reg.defs()}${expand ? "" : bank.defs()}${masks.join("")}</defs>` +
    (bg !== "none" ? `<rect x="0" y="0" width="${W}" height="${H}" fill="${bg}"/>` : "") +
    `<g style="isolation:isolate">${body.join("")}</g></svg>`;
}

function tilePreviewSVG(P) {
  const reg = new GradReg();
  const m = buildTile(P, reg);
  return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${U} ${U}" width="100%" height="100%" preserveAspectRatio="none">` +
    `<defs>${reg.defs()}</defs><rect width="${U}" height="${U}" fill="#fff"/>${m}</svg>`;
}

/* ---------------- data ---------------- */
let UID = 0, TID = 0;
const LAYER_DEFAULTS = {
  visible: true, role: "paint", maskInvert: false,
  blend: "difference", opacity: 1, seed: 0,
  cols: 6, rows: 6, colMode: "random", rowMode: "random", stripeMode: "even",
  freqMin: 1, freqMax: 8, freqMapX: 0, freqMapY: 0,
  axisBias: 0.7, invertChance: 0.4, voidChance: 0,
  rampMode: "linear", gamma: 1, stepMax: 6, pingPong: true,
  mode: "repeat",
  tileX: 1, tileY: 1, tileMode: "even", tileRot: false, tileFlip: false,
  cells: 12, evenness: 0.5, aspectVar: 0.6, splitAxis: "auto", gap: 0, rotChance: 0.3, flipChance: 0.3,
  x: 0, y: 0, w: 100, h: 100, rot: 0, skew: 0, flipX: false, flipY: false,
};
const newLayer = (over = {}) => ({
  id: ++UID, name: `Layer ${UID}`, ...LAYER_DEFAULTS,
  seed: Math.floor(Math.random() * 1e5), ...over,
});

/* ---------------- look codes ----------------
   A look is stored as the difference from LAYER_DEFAULTS, so codes stay short
   and readable. decode() accepts these and full v7/v8 preset files alike. */
const rnd3 = (v) => (typeof v === "number" && !Number.isInteger(v) ? +v.toFixed(3) : v);

function encodeLook(doc) {
  const L = doc.layers.map((l) => {
    const o = { name: l.name };
    for (const k in LAYER_DEFAULTS) if (l[k] !== LAYER_DEFAULTS[k]) o[k] = rnd3(l[k]);
    return o;
  });
  const T = (doc.tiles || []).map((t) => ({
    n: t.name, on: t.on !== false,
    p: Object.fromEntries(Object.entries(t.params).map(([k, v]) => [k, rnd3(v)])),
  }));
  return JSON.stringify({ v: 10, W: doc.W, H: doc.H, bg: doc.bg, L, T });
}

function decodeLook(str, fresh = true) {
  const d = typeof str === "string" ? JSON.parse(str) : str;
  const rawL = d.L || d.layers || [];
  const rawT = d.T || d.tiles || [];
  const layers = rawL.map((l, i) => ({
    ...LAYER_DEFAULTS, ...l, id: fresh ? ++UID : i + 1,
    name: l.name || `Layer ${i + 1}`,
  }));
  const tiles = rawT.map((t, i) => (t.p
    ? { id: fresh ? ++TID : i + 1, name: t.n, on: t.on !== false, params: t.p }
    : { ...t, id: fresh ? ++TID : i + 1 }));
  return { W: d.W || 1600, H: d.H || 1600, bg: d.bg || "#ffffff", layers, tiles };
}

/* thumbnails are expensive to build, so cache them by code string */
const THUMBS = new Map();
function lookThumb(code) {
  if (THUMBS.has(code)) return THUMBS.get(code);
  let html = "";
  try {
    html = buildSVG(decodeLook(code, false), false)
      .replace(/width="\d+" height="\d+"/, 'width="100%" height="100%"');
  } catch { html = ""; }
  THUMBS.set(code, html);
  return html;
}
const SIZES = [["1:1", 1600, 1600], ["16:9", 2560, 1440], ["9:16", 1440, 2560],
["4:5", 1600, 2000], ["4:3", 3840, 2880], ["3:1", 2400, 800]];
const BLENDS = ["normal", "multiply", "screen", "overlay", "darken", "lighten",
  "color-dodge", "color-burn", "hard-light", "soft-light", "difference", "exclusion"];
const SHAPE_BUDGET = 16000;
const WMODES = ["even", "random", "dyadic", "fib"];
const GROUNDS = [["#ffffff", "White"], ["#808080", "Gray"], ["#000000", "Black"], ["none", "None"]];

/* ---- grain ----
   Three scale characters. Every saved look sits somewhere on this axis; the
   generator now targets the ends deliberately instead of always landing mid. */
const GRAIN = {
  chunky: { cols: [2, 4], rows: [2, 4], freq: [1, 3], tile: [1, 2], cells: [3, 7],
    ramp: ["linear", "linear", "triangle", "gamma"], void: 0.3 },
  medium: { cols: [3, 6], rows: [3, 6], freq: [3, 7], tile: [1, 3], cells: [5, 11],
    ramp: ["linear", "linear", "triangle", "steps", "gamma"], void: 0.22 },
  fine:   { cols: [5, 9], rows: [5, 9], freq: [8, 18], tile: [1, 3], cells: [8, 16],
    ramp: ["linear", "steps", "triangle"], void: 0.12 },
};
/* fib, sine and mixed appear in none of the reference looks — left out here,
   still available by hand in the panels. */
const R_WMODE = ["even", "even", "random", "random", "dyadic", "dyadic"];

function randTile(r, g = "medium") {
  const G = GRAIN[g];
  return {
    seed: rint(r, 0, 99999),
    cols: rint(r, G.cols[0], G.cols[1]), rows: rint(r, G.rows[0], G.rows[1]),
    colMode: pick(R_WMODE, r), rowMode: pick(R_WMODE, r),
    stripeMode: pick(["even", "even", "even", "random"], r),
    freqMin: 1, freqMax: rint(r, G.freq[0], G.freq[1]),
    freqMapX: r() < 0.4 ? rflt(r, -0.8, 0.8) : 0,
    freqMapY: r() < 0.3 ? rflt(r, -0.8, 0.8) : 0,
    axisBias: rflt(r, 0.25, 0.85),
    invertChance: rflt(r, 0.2, 0.6),
    voidChance: r() < G.void ? rflt(r, 0.05, 0.2) : 0,
    rampMode: pick(G.ramp, r),
    gamma: rflt(r, 0.6, 2), stepMax: rint(r, 2, 8), pingPong: r() < 0.75,
  };
}
const randRepeat = (r, g = "medium") => {
  const [lo, hi] = GRAIN[g].tile;
  return {
    mode: "repeat", tileX: rint(r, lo, hi), tileY: rint(r, lo, hi),
    tileMode: pick(["even", "random"], r), tileRot: r() < 0.5, tileFlip: r() < 0.5,
  };
};
const randCollage = (r, g = "medium") => {
  /* occasional panel grid: many even cells with a real gutter between them */
  if (r() < 0.12) return {
    mode: "collage", cells: rint(r, 16, 60), evenness: 1, aspectVar: rflt(r, 0.75, 1),
    splitAxis: "auto", gap: rint(r, 8, 30), rotChance: rflt(r, 0, 0.3), flipChance: rflt(r, 0, 0.4),
  };
  const [lo, hi] = GRAIN[g].cells;
  return {
    mode: "collage", cells: rint(r, lo, hi), evenness: rflt(r, 0.3, 0.85),
    aspectVar: rflt(r, 0.4, 0.95), splitAxis: r() < 0.65 ? "auto" : "random", gap: 0,
    rotChance: rflt(r, 0, 0.5), flipChance: rflt(r, 0, 0.5),
  };
};

/* Which grain each layer in the stack gets. Chunky and contrast are weighted
   heavily — a fine mesh over heavy blocks is where the drama comes from. */
function grainPlan(strategy, n, r) {
  if (strategy === "chunky") return Array.from({ length: n }, () => (r() < 0.75 ? "chunky" : "medium"));
  if (strategy === "fine") return Array.from({ length: n }, () => (r() < 0.7 ? "fine" : "medium"));
  if (strategy === "medium") return Array.from({ length: n }, () => "medium");
  if (strategy === "graded") {
    const up = r() < 0.5;
    const order = ["chunky", "medium", "fine"];
    return Array.from({ length: n }, (_, i) => {
      const t = n === 1 ? 0 : i / (n - 1);
      return order[Math.round((up ? t : 1 - t) * 2)];
    });
  }
  /* contrast: base at one extreme, the stack above mostly at the other */
  const baseG = r() < 0.55 ? "chunky" : "fine";
  const other = baseG === "chunky" ? "fine" : "chunky";
  return Array.from({ length: n }, (_, i) => (i === 0 ? baseG : r() < 0.7 ? other : baseG));
}

/* Placement variation. Free rotation and skew expose the master square's
   corners, so anything off-axis is scaled up to keep the frame covered.
   `safe` restricts to right angles and flips, for the base layer. */
function randPlace(r, safe) {
  const o = {};
  if (r() < 0.3) o.flipX = true;
  if (r() < 0.3) o.flipY = true;

  if (safe) {
    if (r() < 0.3) o.rot = pick([90, 180, 270], r);
    return o;
  }

  const roll = r();
  if (roll < 0.2) o.rot = rint(r, -180, 180);
  else if (roll < 0.4) o.rot = pick([90, 180, 270], r);
  if (r() < 0.25) o.skew = rint(r, -24, 24);

  const offAxis = (o.rot && o.rot % 90 !== 0) || o.skew;
  if (offAxis) {
    o.w = rint(r, 150, 190);
    o.h = rint(r, 150, 190);
  } else if (r() < 0.35) {
    o.w = rint(r, 75, 145);
    o.h = rint(r, 75, 145);
  }
  if (r() < 0.3) { o.x = rint(r, -14, 14); o.y = rint(r, -14, 14); }
  return o;
}
const estShapes = (L) => {
  const n = L.mode === "collage" ? L.cells : L.tileX * L.tileY;
  return n * L.cols * L.rows * ((L.freqMin + L.freqMax) / 2) * (1 - L.voidChance);
};
/* trim the heaviest layer until the whole look fits the budget */
function trimToBudget(ls) {
  let guard = 0;
  while (ls.reduce((a, l) => a + estShapes(l), 0) > SHAPE_BUDGET && guard++ < 60) {
    let hi = 0;
    ls.forEach((l, i) => { if (estShapes(l) > estShapes(ls[hi])) hi = i; });
    const L = ls[hi];
    if (L.freqMax > 3) L.freqMax--;
    else if (L.cols > 2) L.cols--;
    else if (L.rows > 2) L.rows--;
    else if (L.mode === "collage" && L.cells > 4) L.cells--;
    else if (L.tileX > 1) L.tileX--;
    else if (L.tileY > 1) L.tileY--;
    else break;
  }
  return ls;
}

/* ---------------- stylesheet ---------------- */
const CSS = `
@import url('https://fonts.googleapis.com/css2?family=Archivo:wght@300;400;500;600&display=swap');
.pd *, .pd *::before, .pd *::after { box-sizing:border-box; }
.pd {
  --bd:#343434; --bd2:#242424; --bd3:#e8e8e8;
  --s0:#0b0b0b; --s1:#141414; --s2:#1e1e1e; --s3:#171717;
  --t0:#eaeaea; --t1:#9c9c9c; --t2:#6b6b6b;
  height:100dvh; width:100%; display:flex; flex-direction:column; overflow:hidden;
  background:var(--s0); color:var(--t0);
  font-family:'Archivo',ui-sans-serif,system-ui,sans-serif;
  font-size:12px; line-height:1.2; -webkit-font-smoothing:antialiased; user-select:none;
}
.pd button { font-family:inherit; background:none; border:none; color:inherit; cursor:pointer; padding:0; }
.pd input, .pd select, .pd textarea { font-family:inherit; }
.pd .cap { font-size:9.5px; font-weight:500; letter-spacing:.1em; text-transform:uppercase; }
.pd .num { font-size:10px; font-family:ui-monospace,SFMono-Regular,Menlo,monospace; font-variant-numeric:tabular-nums; }
.pd .scroll { overflow-y:auto; scrollbar-width:none; -ms-overflow-style:none; }
.pd .scroll::-webkit-scrollbar { width:0; height:0; display:none; }

.pd .top { flex:none; height:44px; display:flex; align-items:center; gap:8px; padding:0 12px;
  border-bottom:1px solid var(--bd2); overflow-x:auto; scrollbar-width:none; }
.pd .top::-webkit-scrollbar { display:none; }
.pd .brand { font-size:11px; font-weight:600; letter-spacing:.24em; text-transform:uppercase; white-space:nowrap; }
.pd .ver { font-size:9px; color:var(--t2); font-family:ui-monospace,monospace; }
.pd .vr { width:1px; height:20px; background:var(--bd2); flex:none; }

.pd .btn { height:28px; padding:0 9px; display:inline-flex; align-items:center; gap:7px;
  border:1px solid var(--bd); color:var(--t1); white-space:nowrap;
  font-size:9.5px; font-weight:500; letter-spacing:.1em; text-transform:uppercase; }
.pd .btn:hover { border-color:#5c5c5c; color:var(--t0); }
.pd .btn.on { border-color:var(--bd3); color:var(--t0); background:var(--s2); }
.pd .btn.dis { opacity:.3; pointer-events:none; }
.pd .btn.hero { border-color:#7a7a7a; color:var(--t0); }
.pd .btn.hero:hover { background:var(--s2); border-color:var(--bd3); }
.pd .chip { height:28px; padding:0 8px; border:1px solid var(--bd2); color:var(--t2);
  font-size:10px; font-family:ui-monospace,monospace; }
.pd .chip:hover { border-color:#5c5c5c; }
.pd .chip.on { border-color:var(--bd3); color:var(--t0); background:var(--s2); }
.pd .iconbtn { color:var(--t1); display:inline-flex; align-items:center; }
.pd .iconbtn:hover { color:var(--t0); }

.pd .num-in { width:64px; height:28px; padding:0 7px; background:var(--s1); border:1px solid var(--bd);
  color:var(--t0); font-size:11px; font-family:ui-monospace,monospace; outline:none; }
.pd .num-in:focus { border-color:#8a8a8a; }
.pd .sel { flex:1; min-width:0; height:26px; padding:0 6px; background:var(--s1); border:1px solid var(--bd);
  color:var(--t0); font-size:11px; outline:none; }
.pd .sel:focus { border-color:#8a8a8a; }
.pd .text-in { flex:1; min-width:0; height:26px; padding:0 7px; background:var(--s1); border:1px solid var(--bd);
  color:var(--t0); font-size:11px; outline:none; }
.pd .text-in:focus { border-color:#8a8a8a; }

.pd .sw { height:28px; padding:0 7px; display:inline-flex; align-items:center; gap:6px; border:1px solid var(--bd2); }
.pd .sw:hover { border-color:#5c5c5c; }
.pd .sw.on { border-color:var(--bd3); background:var(--s2); }
.pd .sw i { width:12px; height:12px; border:1px solid #555; display:block; }
.pd .sw span { font-size:9px; letter-spacing:.05em; text-transform:uppercase; color:var(--t2); }
.pd .sw.on span { color:var(--t0); }

.pd .main { flex:1; min-height:0; display:flex; }
.pd .rail { flex:none; width:76px; min-width:76px; max-width:76px; border-right:1px solid var(--bd2);
  display:flex; flex-direction:column; align-items:center; padding:8px 0; gap:2px; overflow:hidden; }
.pd .railbtn { width:64px; height:50px; display:flex; flex-direction:column; align-items:center;
  justify-content:center; gap:6px; border:1px solid transparent; color:var(--t2); }
.pd .railbtn span { font-size:8.5px; font-weight:500; letter-spacing:.1em; text-transform:uppercase; line-height:1; }
.pd .railbtn:hover { color:var(--t0); background:var(--s3); }
.pd .railbtn.on { color:var(--t0); background:var(--s2); border-color:#4a4a4a; }

.pd .panel { flex:none; width:292px; min-width:292px; max-width:292px; border-right:1px solid var(--bd2);
  display:flex; flex-direction:column; min-height:0; overflow:hidden; }
.pd .panelhead { flex:none; height:32px; display:flex; align-items:center; gap:8px; padding:0 12px;
  border-bottom:1px solid var(--bd2); }
.pd .panelhead .title { font-size:10px; font-weight:600; letter-spacing:.2em; text-transform:uppercase; }
.pd .panelhead .sub { font-size:10px; color:var(--t2); margin-left:auto; max-width:130px;
  overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
.pd .body { flex:1; min-height:0; padding:10px 12px; }

.pd .row { display:flex; align-items:center; gap:10px; height:30px; }
.pd .row > .lab { flex:none; width:80px; font-size:9.5px; letter-spacing:.08em; text-transform:uppercase;
  color:var(--t1); overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
.pd .row > .ctl { flex:1; min-width:0; display:flex; align-items:center; gap:8px; }
.pd .note { font-size:10px; line-height:1.5; color:var(--t2); margin:10px 0 0; }
.pd .stack { display:flex; flex-wrap:wrap; gap:6px; padding-top:10px; }
.pd .sect { font-size:9px; letter-spacing:.18em; text-transform:uppercase; color:var(--t2);
  border-bottom:1px solid var(--bd2); padding-bottom:5px; margin:12px 0 6px; }

/* custom slider */
.pd .trk { position:relative; flex:1; min-width:0; height:16px; display:flex; align-items:center;
  cursor:ew-resize; touch-action:none; outline:none; }
.pd .trk .bar { position:absolute; left:0; right:0; height:2px; background:#3e3e3e; }
.pd .trk .fill { position:absolute; left:0; height:2px; background:#6f6f6f; }
.pd .trk .knob { position:absolute; width:9px; height:9px; background:var(--t0); margin-left:-4.5px; }
.pd .trk:hover .knob { box-shadow:0 0 0 3px rgba(255,255,255,.12); }
.pd .trk:focus-visible .knob { box-shadow:0 0 0 3px rgba(255,255,255,.3); }
.pd .vin { flex:none; width:48px; height:22px; background:var(--s1); border:1px solid var(--bd2);
  color:var(--t1); font-size:10px; font-family:ui-monospace,monospace; text-align:right;
  padding:0 5px; outline:none; user-select:text; }
.pd .vin:focus { border-color:#8a8a8a; color:var(--t0); }

.pd .layers { flex:none; border-top:1px solid var(--bd2); }
.pd .layershead { height:30px; display:flex; align-items:center; gap:10px; padding:0 12px; }
.pd .layershead .title { font-size:9.5px; font-weight:500; letter-spacing:.18em; text-transform:uppercase;
  color:var(--t1); margin-right:auto; }
.pd .layerlist { max-height:150px; padding-bottom:4px; }
.pd .layeritem { display:flex; align-items:center; gap:8px; height:28px; padding:0 12px; cursor:pointer;
  border-left:2px solid transparent; }
.pd .layeritem:hover { background:var(--s3); }
.pd .layeritem.on { background:var(--s2); border-left-color:var(--bd3); }
.pd .layeritem .nm { flex:1; min-width:0; font-size:11px; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
.pd .layeritem .md { font-size:9px; font-family:ui-monospace,monospace; color:var(--t2); }
.pd .layeritem .vis { color:var(--t1); display:flex; }
.pd .layeritem .vis.off { color:#3d3d3d; }

/* tile bank */
.pd .tilegrid { display:grid; grid-template-columns:repeat(3,1fr); gap:8px; }
.pd .lookgrid { display:grid; grid-template-columns:repeat(2,1fr); gap:8px; }
.pd .lookcard { border:1px solid var(--bd2); background:var(--s1); }
.pd .lookcard:hover { border-color:#5c5c5c; }
.pd .lookcard .thumb { width:100%; aspect-ratio:16/10; overflow:hidden; background:#0f0f0f;
  display:block; cursor:pointer; }
.pd .codebox { width:100%; height:66px; padding:6px; resize:none; outline:none; background:var(--s1);
  border:1px solid var(--bd2); color:var(--t1); font-size:9.5px; font-family:ui-monospace,monospace;
  line-height:1.4; user-select:text; scrollbar-width:none; }
.pd .codebox::-webkit-scrollbar { display:none; }
.pd .codebox:focus { border-color:#8a8a8a; color:var(--t0); }
.pd .tilecard { border:1px solid var(--bd2); background:var(--s1); }
.pd .tilecard.on { border-color:var(--bd3); }
.pd .tilecard .thumb { width:100%; aspect-ratio:1/1; overflow:hidden; background:#fff; display:block; }
.pd .tilecard .bar2 { display:flex; align-items:center; gap:4px; padding:3px 4px; }
.pd .tilecard .bar2 span { flex:1; min-width:0; font-size:9px; color:var(--t2); overflow:hidden;
  text-overflow:ellipsis; white-space:nowrap; }
.pd .empty { font-size:10px; color:var(--t2); line-height:1.6; }

.pd .stage { flex:1; min-width:0; min-height:0; position:relative; display:flex; align-items:center;
  justify-content:center; background:var(--s1); overflow:hidden; }
.pd .art { position:relative; border:1px solid #3a3a3a; overflow:hidden; }
.pd .art > div { position:absolute; inset:0; }
.pd .toast { position:absolute; right:12px; bottom:8px; padding:5px 9px; pointer-events:none;
  background:rgba(11,11,11,.88); border:1px solid var(--bd2); color:var(--t1);
  font-size:9.5px; font-family:ui-monospace,monospace; opacity:0; transition:opacity .16s ease; }
.pd .toast.on { opacity:1; }
.pd .readout { position:absolute; left:12px; bottom:8px; font-size:9px; font-family:ui-monospace,monospace; color:var(--t2); }

.pd .drawer { position:absolute; inset:0; background:rgba(11,11,11,.96); display:flex; flex-direction:column; }
.pd .drawerhead { flex:none; height:36px; display:flex; align-items:center; gap:8px; padding:0 12px;
  border-bottom:1px solid var(--bd2); }
.pd .drawerhead .title { font-size:10px; font-weight:600; letter-spacing:.2em; text-transform:uppercase; margin-right:auto; }
.pd .drawerbody { flex:1; min-height:0; padding:12px; display:flex; flex-direction:column; gap:8px; }
.pd .src { flex:1; min-height:0; width:100%; padding:8px; resize:none; outline:none; background:var(--s1);
  border:1px solid var(--bd2); color:var(--t1); font-size:10px; font-family:ui-monospace,monospace;
  line-height:1.45; user-select:text; scrollbar-width:none; }
.pd .src::-webkit-scrollbar { display:none; }
.pd .pngbox { flex:1; min-height:0; display:flex; align-items:center; justify-content:center;
  background:var(--s1); border:1px solid var(--bd2); overflow:hidden; }
.pd .pngbox img { max-width:100%; max-height:100%; object-fit:contain; }
`;

/* ---------------- icons ---------------- */
const I = ({ d, size = 18 }) => (
  <svg width={size} height={size} viewBox="0 0 24 24" fill="none" stroke="currentColor"
    strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" aria-hidden="true">{d}</svg>
);
const Ico = {
  grid: <I d={<><rect x="3" y="3" width="18" height="18" /><path d="M9 3v18M15 3v18M3 9h18M3 15h18" /></>} size={20} />,
  stripe: <I d={<path d="M4 4v16M8 4v16M11 4v16M15 4v16M20 4v16" />} size={20} />,
  ramp: <I d={<><rect x="3" y="4" width="18" height="16" /><path d="M3 20 21 4" /></>} size={20} />,
  layout: <I d={<><rect x="3" y="3" width="18" height="18" /><path d="M3 10h11M14 3v18M14 15h7" /></>} size={20} />,
  place: <I d={<path d="M12 3v18M3 12h18M12 3 9 6M12 3l3 3M12 21l-3-3M12 21l3-3M3 12l3-3M3 12l3 3M21 12l-3-3M21 12l-3 3" />} size={20} />,
  layers: <I d={<><path d="M12 3 3 8l9 5 9-5-9-5Z" /><path d="M3 13l9 5 9-5" /></>} size={20} />,
  bank: <I d={<><rect x="3" y="3" width="7" height="7" /><rect x="14" y="3" width="7" height="7" /><rect x="3" y="14" width="7" height="7" /><path d="M14 17.5h7M17.5 14v7" /></>} size={20} />,
  eye: <I d={<><path d="M2 12s3.5-6 10-6 10 6 10 6-3.5 6-10 6-10-6-10-6Z" /><circle cx="12" cy="12" r="2.6" /></>} size={14} />,
  eyeOff: <I d={<><path d="M4 4l16 16" /><path d="M9.6 6.4A9.9 9.9 0 0 1 12 6c6.5 0 10 6 10 6a17 17 0 0 1-3.3 3.9M6.3 8.2A17 17 0 0 0 2 12s3.5 6 10 6a9.7 9.7 0 0 0 3.1-.5" /></>} size={14} />,
  add: <I d={<path d="M12 5v14M5 12h14" />} size={15} />,
  copy: <I d={<><rect x="8" y="3" width="13" height="13" /><path d="M16 19v2H3V8h2" /></>} size={15} />,
  trash: <I d={<path d="M4 7h16M9 7V4h6v3M6 7l1 13h10l1-13" />} size={15} />,
  up: <I d={<path d="M6 15l6-6 6 6" />} size={15} />,
  down: <I d={<path d="M6 9l6 6 6-6" />} size={15} />,
  dice: <I d={<><rect x="3" y="3" width="18" height="18" rx="2" /><circle cx="8" cy="8" r="1.1" fill="currentColor" /><circle cx="16" cy="16" r="1.1" fill="currentColor" /><circle cx="12" cy="12" r="1.1" fill="currentColor" /></>} size={15} />,
  spark: <I d={<><path d="M12 3v5M12 16v5M3 12h5M16 12h5M6 6l3 3M15 15l3 3M18 6l-3 3M9 15l-3 3" /></>} size={15} />,
  code: <I d={<path d="M9 7 4 12l5 5M15 7l5 5-5 5" />} size={15} />,
  image: <I d={<><rect x="3" y="4" width="18" height="16" /><circle cx="8.5" cy="9" r="1.5" /><path d="m3 17 5-5 4 4 3-3 6 6" /></>} size={15} />,
  save: <I d={<><path d="M4 4h12l4 4v12H4z" /><path d="M8 4v5h7M8 20v-6h8v6" /></>} size={15} />,
  open: <I d={<path d="M3 7h6l2 2h10v10H3z" />} size={15} />,
  close: <I d={<path d="M6 6l12 12M18 6 6 18" />} size={16} />,
  reset: <I d={<><path d="M3 12a9 9 0 1 0 3-6.7" /><path d="M3 4v5h5" /></>} size={15} />,
  snap: <I d={<><rect x="5" y="5" width="14" height="14" /><path d="M5 12h14M12 5v14" /></>} size={15} />,
  looks: <I d={<><path d="M5 3h14v18l-7-5-7 5V3Z" /><path d="M9 8h6" /></>} size={20} />,
  undo: <I d={<><path d="M4 8h11a5 5 0 0 1 0 10h-6" /><path d="M8 4 4 8l4 4" /></>} size={15} />,
  redo: <I d={<><path d="M20 8H9a5 5 0 0 0 0 10h6" /><path d="m16 4 4 4-4 4" /></>} size={15} />,
  bake: <I d={<><path d="M12 3v11" /><path d="M8 10l4 4 4-4" /><rect x="3" y="17" width="18" height="4" /></>} size={15} />,
};

/* ---------------- slider ---------------- */
function Slider({ v, set, min, max, step = 1 }) {
  const trk = useRef(null);
  const drag = useRef(null);
  const [txt, setTxt] = useState(null);
  const dec = useMemo(() => (String(step).includes(".") ? String(step).split(".")[1].length : 0), [step]);

  const clamp = useCallback((x) => {
    const q = Math.round((x - min) / step) * step + min;
    return +Math.min(max, Math.max(min, q)).toFixed(dec);
  }, [min, max, step, dec]);

  const valAt = useCallback((clientX) => {
    const r = trk.current.getBoundingClientRect();
    return clamp(min + ((clientX - r.left) / Math.max(1, r.width)) * (max - min));
  }, [clamp, min, max]);

  const onDown = (e) => {
    e.preventDefault();
    trk.current.focus();
    trk.current.setPointerCapture(e.pointerId);
    const start = valAt(e.clientX);
    drag.current = { x: e.clientX, v: start };
    set(start);
  };
  const onMove = (e) => {
    if (!drag.current) return;
    const r = trk.current.getBoundingClientRect();
    /* Shift = fine drag at 1/6 sensitivity, so every step is reachable
       even when the range is wider than the track is in pixels. */
    const perPx = ((max - min) / Math.max(1, r.width)) * (e.shiftKey ? 0.16 : 1);
    set(clamp(drag.current.v + (e.clientX - drag.current.x) * perPx));
  };
  const onUp = (e) => {
    drag.current = null;
    try { trk.current.releasePointerCapture(e.pointerId); } catch { }
  };

  /* wheel needs a non-passive listener to be able to preventDefault */
  useEffect(() => {
    const el = trk.current; if (!el) return;
    const h = (e) => {
      e.preventDefault();
      const dir = (e.deltaY || e.deltaX) > 0 ? -1 : 1;
      set(clamp(v + dir * step * (e.shiftKey ? 10 : 1)));
    };
    el.addEventListener("wheel", h, { passive: false });
    return () => el.removeEventListener("wheel", h);
  }, [v, step, clamp, set]);

  const onKey = (e) => {
    const big = e.shiftKey ? 10 : 1;
    if (e.key === "ArrowRight" || e.key === "ArrowUp") { e.preventDefault(); set(clamp(v + step * big)); }
    else if (e.key === "ArrowLeft" || e.key === "ArrowDown") { e.preventDefault(); set(clamp(v - step * big)); }
    else if (e.key === "Home") { e.preventDefault(); set(min); }
    else if (e.key === "End") { e.preventDefault(); set(max); }
  };

  const commit = () => {
    const n = parseFloat(txt);
    if (!Number.isNaN(n)) set(clamp(n));
    setTxt(null);
  };

  const pct = ((v - min) / (max - min)) * 100;
  return (
    <>
      <div className="trk" ref={trk} tabIndex={0} role="slider"
        aria-valuenow={v} aria-valuemin={min} aria-valuemax={max}
        onPointerDown={onDown} onPointerMove={onMove} onPointerUp={onUp} onPointerCancel={onUp} onKeyDown={onKey}>
        <span className="bar" />
        <span className="fill" style={{ width: `${pct}%` }} />
        <span className="knob" style={{ left: `${pct}%` }} />
      </div>
      <input className="vin" value={txt ?? (dec ? v.toFixed(dec) : v)}
        onChange={(e) => setTxt(e.target.value)}
        onFocus={(e) => { setTxt(String(dec ? v.toFixed(dec) : v)); e.target.select(); }}
        onBlur={commit}
        onKeyDown={(e) => { if (e.key === "Enter") e.currentTarget.blur(); if (e.key === "Escape") setTxt(null); }} />
    </>
  );
}

/* ---------------- atoms ---------------- */
const Row = ({ label, children }) => (
  <div className="row"><div className="lab">{label}</div><div className="ctl">{children}</div></div>
);
const Sel = ({ v, set, opts }) => (
  <select className="sel" value={v} onChange={(e) => set(e.target.value)}>
    {opts.map((o) => <option key={o} value={o}>{o}</option>)}
  </select>
);
const Toggle = ({ v, set, label }) => (
  <button className={`btn${v ? " on" : ""}`} onClick={() => set(!v)}>{label}</button>
);
const Act = ({ onClick, icon, label, on, hero, dis }) => (
  <button className={`btn${on ? " on" : ""}${hero ? " hero" : ""}${dis ? " dis" : ""}`}
    onClick={onClick} disabled={dis} title={label}>
    {icon}<span>{label}</span>
  </button>
);

/* ---------------- artboard (double buffered) ---------------- */
const Artboard = React.memo(function Artboard({ svg, w, h }) {
  const html = useMemo(() => svg.replace(/width="\d+" height="\d+"/, 'width="100%" height="100%"'), [svg]);
  const a = useRef(null), b = useRef(null);
  const front = useRef(0);
  const [, tick] = useReducer((x) => x + 1, 0);

  /* Write the new markup into the hidden buffer, then swap on the next frame.
     Replacing innerHTML in place is what caused the white flash. */
  useEffect(() => {
    const backIdx = 1 - front.current;
    const back = backIdx === 0 ? a.current : b.current;
    if (!back) return;
    back.innerHTML = html;
    const id = requestAnimationFrame(() => { front.current = backIdx; tick(); });
    return () => cancelAnimationFrame(id);
  }, [html]);

  return (
    <div className="art" style={{ width: w, height: h }}>
      <div ref={a} style={{ opacity: front.current === 0 ? 1 : 0 }} />
      <div ref={b} style={{ opacity: front.current === 1 ? 1 : 0 }} />
    </div>
  );
});

/* ---------------- export helpers ---------------- */
const svgDataUrl = (s) => "data:image/svg+xml;charset=utf-8," + encodeURIComponent(s);
function tryDownload(href, name) {
  try {
    const a = document.createElement("a");
    a.href = href; a.download = name; a.rel = "noopener";
    document.body.appendChild(a); a.click(); a.remove(); return true;
  } catch { return false; }
}
async function copyText(t) {
  try { await navigator.clipboard.writeText(t); return true; } catch { }
  try {
    const ta = document.createElement("textarea");
    ta.value = t; ta.style.cssText = "position:fixed;top:0;left:0;opacity:0";
    document.body.appendChild(ta); ta.focus(); ta.select();
    const ok = document.execCommand("copy"); ta.remove(); return ok;
  } catch { return false; }
}

const TABS = [["Grid", Ico.grid], ["Stripe", Ico.stripe], ["Ramp", Ico.ramp],
["Layout", Ico.layout], ["Place", Ico.place], ["Layer", Ico.layers],
["Tiles", Ico.bank], ["Looks", Ico.looks]];

/* ---------------- app ---------------- */
export default function PDLoomRift() {
  const [W, setW] = useState(1600);
  const [H, setH] = useState(1600);
  const [bg, setBg] = useState("#ffffff");
  const [layers, setLayers] = useState([newLayer({ name: "Base" })]);
  const [tiles, setTiles] = useState([]);
  const [looks, setLooks] = useState([]);
  const [lookName, setLookName] = useState("");
  const [importCode, setImportCode] = useState("");
  const [sel, setSel] = useState(1);
  const [tab, setTab] = useState("Grid");
  const [expand, setExpand] = useState(true);
  const [msg, setMsg] = useState("");
  const [drawer, setDrawer] = useState(null);
  const [png, setPng] = useState(null);
  const fileRef = useRef(null);
  const stageRef = useRef(null);
  const [fit, setFit] = useState({ w: 200, h: 200 });

  const doc = useMemo(() => ({ W, H, bg, layers, tiles }), [W, H, bg, layers, tiles]);
  const previewDoc = useDeferredValue(doc);
  const svg = useMemo(() => buildSVG(previewDoc, false), [previewDoc]);
  const rectCount = useMemo(() => (svg.match(/<rect/g) || []).length, [svg]);
  const L = layers.find((l) => l.id === sel) || layers[0];

  /* saved looks persist in localStorage */
  useEffect(() => {
    (async () => {
      try {
        const raw = localStorage.getItem("pd_loomrift_looks")
          || localStorage.getItem("pd_loomforge_looks")
          || localStorage.getItem("pd_tileforge_looks");
        if (raw) setLooks(JSON.parse(raw));
      } catch { /* corrupt or unavailable — start empty */ }
    })();
  }, []);

  useEffect(() => {
    if (document.getElementById("pd-archivo")) return;
    const pre = document.createElement("link");
    pre.rel = "preconnect"; pre.href = "https://fonts.gstatic.com"; pre.crossOrigin = "";
    const link = document.createElement("link");
    link.id = "pd-archivo"; link.rel = "stylesheet";
    link.href = "https://fonts.googleapis.com/css2?family=Archivo:wght@300;400;500;600&display=swap";
    document.head.append(pre, link);
  }, []);

  useEffect(() => {
    const el = stageRef.current; if (!el) return;
    const calc = () => {
      const r = el.getBoundingClientRect();
      const s = Math.min((r.width - 48) / W, (r.height - 48) / H);
      setFit({ w: Math.max(40, W * s), h: Math.max(40, H * s) });
    };
    calc();
    const ro = new ResizeObserver(calc); ro.observe(el);
    return () => ro.disconnect();
  }, [W, H]);

  const up = useCallback((patch) => setLayers((ls) => ls.map((l) => (l.id === sel ? { ...l, ...patch } : l))), [sel]);
  const flash = (t) => { setMsg(t); setTimeout(() => setMsg(""), 1800); };

  /* ---- random look ----
     Composes from a few known-good arrangements rather than randomising freely.
     Blend mode is never assigned here — every layer keeps the difference
     default until it is changed by hand in the Layer tab. */
  const randomLook = () => {
    const r = mulberry32(Math.floor(Math.random() * 1e9));

    /* Strategy first, then depth — chunky stacks stay shallow so the blocks
       still read, fine ones can go deeper before they turn to mud. */
    const strategy = pick([
      "chunky", "chunky", "chunky",
      "contrast", "contrast", "contrast",
      "graded", "medium", "fine",
    ], r);
    const n = strategy === "chunky" ? pick([2, 2, 3, 3, 4], r)
      : strategy === "fine" ? pick([3, 3, 4, 4, 5], r)
        : pick([2, 3, 3, 4, 4], r);
    const plan = grainPlan(strategy, n, r);

    const ls = plan.map((g, i) => {
      const base = i === 0;
      /* chunky layers lean to repeat, fine ones take collage more often */
      const collageOdds = g === "chunky" ? 0.28 : g === "fine" ? 0.5 : 0.4;
      return newLayer({
        name: base ? "Base" : `Layer ${i + 1}`,
        ...randTile(r, g),
        ...(r() < collageOdds ? randCollage(r, g) : randRepeat(r, g)),
        opacity: base ? 1 : (r() < 0.6 ? 1 : +rflt(r, 0.5, 0.95).toFixed(2)),
        ...randPlace(r, base),
      });
    });

    trimToBudget(ls);
    setLayers(ls); setSel(ls[0].id);
    flash(`${strategy} · ${n} layers`);
  };

  /* ---- history ----
     Snapshots are taken on a trailing debounce, so a whole slider drag collapses
     into one undo step rather than hundreds. */
  const hist = useRef({ stack: [], i: -1 });
  const skipSnap = useRef(false);
  const [, bumpHist] = useReducer((x) => x + 1, 0);

  useEffect(() => {
    if (skipSnap.current) { skipSnap.current = false; return; }
    const t = setTimeout(() => {
      const snap = JSON.stringify({ W, H, bg, layers, tiles });
      const h = hist.current;
      if (h.stack[h.i] === snap) return;
      h.stack = h.stack.slice(0, h.i + 1);
      h.stack.push(snap);
      if (h.stack.length > 80) h.stack.shift();
      h.i = h.stack.length - 1;
      bumpHist();
    }, 420);
    return () => clearTimeout(t);
  }, [W, H, bg, layers, tiles]);

  const restore = (snap) => {
    skipSnap.current = true;
    const d = JSON.parse(snap);
    setW(d.W); setH(d.H); setBg(d.bg); setLayers(d.layers); setTiles(d.tiles);
    if (!d.layers.some((l) => l.id === sel)) setSel(d.layers[0]?.id);
    bumpHist();
  };
  const canUndo = hist.current.i > 0;
  const canRedo = hist.current.i >= 0 && hist.current.i < hist.current.stack.length - 1;
  const undo = () => { const h = hist.current; if (h.i <= 0) return; h.i--; restore(h.stack[h.i]); };
  const redo = () => { const h = hist.current; if (h.i >= h.stack.length - 1) return; h.i++; restore(h.stack[h.i]); };

  useEffect(() => {
    const onKey = (e) => {
      const mod = e.metaKey || e.ctrlKey;
      if (!mod || e.key.toLowerCase() !== "z") return;
      const tag = document.activeElement?.tagName;
      if (tag === "INPUT" || tag === "TEXTAREA") return;
      e.preventDefault();
      e.shiftKey ? redo() : undo();
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  });

  /* ---- look library ---- */
  const persistLooks = async (list) => {
    setLooks(list);
    try { localStorage.setItem("pd_loomrift_looks", JSON.stringify(list)); } catch { }
  };
  const saveLook = () => {
    const code = encodeLook(doc);
    const name = lookName.trim() || `Look ${looks.length + 1}`;
    persistLooks([...looks, { id: Date.now(), name, code }]);
    setLookName("");
    flash(`Saved "${name}"`);
  };
  const applyLook = (code, label) => {
    try {
      const d = decodeLook(code);
      setW(d.W); setH(d.H); setBg(d.bg);
      setLayers(d.layers); setTiles(d.tiles); setSel(d.layers[0]?.id);
      flash(label || "Look loaded");
    } catch { flash("That code isn't valid"); }
  };
  const delLook = (id) => persistLooks(looks.filter((l) => l.id !== id));
  const copyLook = async (code) =>
    flash((await copyText(code)) ? "Code copied" : "Clipboard blocked — select and copy");
  const doImport = () => {
    if (!importCode.trim()) return;
    try {
      const d = decodeLook(importCode.trim());
      const name = `Imported ${looks.length + 1}`;
      persistLooks([...looks, { id: Date.now(), name, code: encodeLook({ ...d, tiles: d.tiles }) }]);
      setImportCode("");
      applyLook(importCode.trim(), `Imported "${name}"`);
    } catch { flash("That code isn't valid"); }
  };

  /* ---- tile bank ---- */
  const bakeTile = () => {
    const t = { id: ++TID, name: L.name, params: genParams(L), on: true };
    setTiles((ts) => [...ts, t]);
    flash(`Baked "${t.name}" to tiles`);
  };
  const delTile = (id) => setTiles((ts) => ts.filter((t) => t.id !== id));
  const toggleTile = (id) => setTiles((ts) => ts.map((t) => (t.id === id ? { ...t, on: !t.on } : t)));

  /* ---- export ---- */
  const openSVG = () => { tryDownload(svgDataUrl(buildSVG(doc, expand)), `PD_LoomRift_${Date.now()}.svg`); setDrawer("svg"); };
  const openPNG = () => {
    setDrawer("png"); setPng(null);
    const img = new Image();
    img.onload = () => {
      try {
        const c = document.createElement("canvas");
        c.width = W; c.height = H;
        c.getContext("2d").drawImage(img, 0, 0, W, H);
        const url = c.toDataURL("image/png");
        setPng(url); tryDownload(url, `PD_LoomRift_${Date.now()}.png`);
      } catch { setPng("error"); }
    };
    img.onerror = () => setPng("error");
    img.src = svgDataUrl(buildSVG(doc, true));
  };
  const presetJSON = () => JSON.stringify({ v: 8, W, H, bg, layers, tiles }, null, 1);
  const openPreset = () => {
    tryDownload("data:application/json;charset=utf-8," + encodeURIComponent(presetJSON()), "PD_LoomRift_preset.json");
    setDrawer("preset");
  };
  const loadJSON = (e) => {
    const f = e.target.files?.[0]; if (!f) return;
    const rd = new FileReader();
    rd.onload = () => {
      try {
        const d = JSON.parse(rd.result);
        setW(d.W); setH(d.H); setBg(d.bg || "#ffffff");
        const ls = d.layers.map((l) => ({ ...newLayer(), ...l, id: ++UID }));
        setTiles((d.tiles || []).map((t) => ({ ...t, id: ++TID })));
        setLayers(ls); setSel(ls[0]?.id); flash("Preset loaded");
      } catch { flash("Couldn't read that file"); }
    };
    rd.readAsText(f); e.target.value = "";
  };

  const addLayer = () => { const n = newLayer(); setLayers((ls) => [...ls, n]); setSel(n.id); setTab("Layer"); };
  const dupLayer = () => { const n = { ...L, id: ++UID, name: L.name + " copy" }; setLayers((ls) => [...ls, n]); setSel(n.id); };
  const delLayer = () => {
    if (layers.length < 2) return;
    const i = layers.findIndex((l) => l.id === sel);
    const ls = layers.filter((l) => l.id !== sel);
    setLayers(ls); setSel(ls[Math.max(0, i - 1)].id);
  };
  const move = (d) => {
    const i = layers.findIndex((l) => l.id === sel), j = i + d;
    if (j < 0 || j >= layers.length) return;
    const ls = [...layers]; [ls[i], ls[j]] = [ls[j], ls[i]]; setLayers(ls);
  };

  const drawerText = drawer === "svg" ? buildSVG(doc, expand) : drawer === "preset" ? presetJSON() : "";
  const activeTiles = tiles.filter((t) => t.on).length;

  return (
    <div className="pd">
      <style>{CSS}</style>

      {/* ---- document bar ---- */}
      <div className="top">
        <span className="brand">PD_LoomRift</span>
        <span className="ver">1.5</span>
        <span className="vr" />
        <div style={{ display: "flex", gap: 3 }}>
          {SIZES.map(([n, w, h]) => (
            <button key={n} className={`chip${W === w && H === h ? " on" : ""}`} onClick={() => { setW(w); setH(h); }}>{n}</button>
          ))}
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: 5 }}>
          <input className="num-in" type="number" value={W} min={200} max={8000}
            onChange={(e) => setW(Math.max(200, +e.target.value || 200))} />
          <span style={{ color: "var(--t2)", fontSize: 10 }}>×</span>
          <input className="num-in" type="number" value={H} min={200} max={8000}
            onChange={(e) => setH(Math.max(200, +e.target.value || 200))} />
        </div>
        <span className="vr" />
        <div style={{ display: "flex", alignItems: "center", gap: 4 }}>
          <span className="cap" style={{ color: "var(--t1)", whiteSpace: "nowrap" }}>Background</span>
          {GROUNDS.map(([g, gl]) => (
            <button key={g} className={`sw${bg === g ? " on" : ""}`} onClick={() => setBg(g)} title={`Background: ${gl}`}>
              <i style={g === "none"
                ? { backgroundImage: "linear-gradient(45deg,#555 25%,transparent 25%,transparent 75%,#555 75%),linear-gradient(45deg,#555 25%,#1a1a1a 25%,#1a1a1a 75%,#555 75%)", backgroundSize: "8px 8px", backgroundPosition: "0 0,4px 4px" }
                : { background: g }} />
              <span>{gl}</span>
            </button>
          ))}
        </div>
        <span style={{ flex: 1 }} />
        <Act onClick={undo} icon={Ico.undo} label="Undo" dis={!canUndo} />
        <Act onClick={redo} icon={Ico.redo} label="Redo" dis={!canRedo} />
        <span className="vr" />
        <Act onClick={randomLook} icon={Ico.spark} label="Random look" hero />
        <Act onClick={() => setLayers((ls) => ls.map((l) => ({ ...l, seed: Math.floor(Math.random() * 1e5) })))} icon={Ico.dice} label="Reseed all" />
        <span className="vr" />
        <Act onClick={openSVG} icon={Ico.code} label="SVG" />
        <Act onClick={openPNG} icon={Ico.image} label="PNG" />
        <Act onClick={openPreset} icon={Ico.save} label="Save" />
        <Act onClick={() => fileRef.current?.click()} icon={Ico.open} label="Load" />
        <input ref={fileRef} type="file" accept=".json" onChange={loadJSON} style={{ display: "none" }} />
      </div>

      <div className="main">
        <div className="rail">
          {TABS.map(([t, icon]) => (
            <button key={t} className={`railbtn${tab === t ? " on" : ""}`} onClick={() => setTab(t)} title={t}>
              {icon}<span>{t}</span>
            </button>
          ))}
        </div>

        <div className="panel">
          <div className="panelhead">
            <span className="title">{tab}</span>
            <span className="sub">{tab === "Tiles" ? `${tiles.length} baked` : tab === "Looks" ? `${looks.length} saved` : L?.name}</span>
          </div>

          <div className="body scroll">
            {L && tab === "Grid" && (<>
              <Row label="Columns"><Slider v={L.cols} set={(v) => up({ cols: v })} min={1} max={40} /></Row>
              <Row label="Col rhythm"><Sel v={L.colMode} set={(v) => up({ colMode: v })} opts={WMODES} /></Row>
              <Row label="Rows"><Slider v={L.rows} set={(v) => up({ rows: v })} min={1} max={40} /></Row>
              <Row label="Row rhythm"><Sel v={L.rowMode} set={(v) => up({ rowMode: v })} opts={WMODES} /></Row>
              <Row label="Voids"><Slider v={L.voidChance} set={(v) => up({ voidChance: v })} min={0} max={0.8} step={0.01} /></Row>
              <Row label="Seed"><Slider v={L.seed} set={(v) => up({ seed: v })} min={0} max={99999} /></Row>
              <div className="stack">
                <Act onClick={() => up({ seed: Math.floor(Math.random() * 1e5) })} icon={Ico.dice} label="Reseed layer" />
                <Act onClick={bakeTile} icon={Ico.bake} label="Bake to tile" />
              </div>
            </>)}

            {L && tab === "Stripe" && (<>
              <Row label="Min count"><Slider v={L.freqMin} set={(v) => up({ freqMin: v, freqMax: Math.max(v, L.freqMax) })} min={1} max={60} /></Row>
              <Row label="Max count"><Slider v={L.freqMax} set={(v) => up({ freqMax: v, freqMin: Math.min(v, L.freqMin) })} min={1} max={60} /></Row>
              <Row label="Widths"><Sel v={L.stripeMode} set={(v) => up({ stripeMode: v })} opts={WMODES} /></Row>
              <Row label="Density ↔"><Slider v={L.freqMapX} set={(v) => up({ freqMapX: v })} min={-1} max={1} step={0.05} /></Row>
              <Row label="Density ↕"><Slider v={L.freqMapY} set={(v) => up({ freqMapY: v })} min={-1} max={1} step={0.05} /></Row>
              <Row label="Vert bias"><Slider v={L.axisBias} set={(v) => up({ axisBias: v })} min={0} max={1} step={0.01} /></Row>
            </>)}

            {L && tab === "Ramp" && (<>
              <Row label="Shape"><Sel v={L.rampMode} set={(v) => up({ rampMode: v })} opts={[...RAMPS, "mixed"]} /></Row>
              <Row label="Gamma"><Slider v={L.gamma} set={(v) => up({ gamma: v })} min={0.2} max={4} step={0.05} /></Row>
              <Row label="Max steps"><Slider v={L.stepMax} set={(v) => up({ stepMax: v })} min={2} max={16} /></Row>
              <Row label="Inverts"><Slider v={L.invertChance} set={(v) => up({ invertChance: v })} min={0} max={1} step={0.01} /></Row>
              <div className="stack"><Toggle v={L.pingPong} set={(v) => up({ pingPong: v })} label="Ping-pong direction" /></div>
            </>)}

            {L && tab === "Layout" && (<>
              <Row label="Mode"><Sel v={L.mode} set={(v) => up({ mode: v })} opts={["repeat", "collage"]} /></Row>
              {L.mode === "repeat" ? (<>
                <div className="sect">Uniform repeat</div>
                <Row label="Across"><Slider v={L.tileX} set={(v) => up({ tileX: v })} min={1} max={16} /></Row>
                <Row label="Down"><Slider v={L.tileY} set={(v) => up({ tileY: v })} min={1} max={16} /></Row>
                <Row label="Cell sizes"><Sel v={L.tileMode} set={(v) => up({ tileMode: v })} opts={WMODES} /></Row>
                <div className="stack">
                  <Toggle v={L.tileRot} set={(v) => up({ tileRot: v })} label="Rotate 90°" />
                  <Toggle v={L.tileFlip} set={(v) => up({ tileFlip: v })} label="Flip" />
                </div>
              </>) : (<>
                <div className="sect">Collage packing</div>
                <Row label="Cells"><Slider v={L.cells} set={(v) => up({ cells: v })} min={1} max={60} /></Row>
                <Row label="Evenness"><Slider v={L.evenness} set={(v) => up({ evenness: v })} min={0} max={1} step={0.01} /></Row>
                <Row label="Ratio range"><Slider v={L.aspectVar} set={(v) => up({ aspectVar: v })} min={0} max={1} step={0.01} /></Row>
                <Row label="Split axis"><Sel v={L.splitAxis} set={(v) => up({ splitAxis: v })} opts={["auto", "random"]} /></Row>
                <Row label="Gap"><Slider v={L.gap} set={(v) => up({ gap: v })} min={0} max={60} /></Row>
                <Row label="Rotate %"><Slider v={L.rotChance} set={(v) => up({ rotChance: v })} min={0} max={1} step={0.01} /></Row>
                <Row label="Flip %"><Slider v={L.flipChance} set={(v) => up({ flipChance: v })} min={0} max={1} step={0.01} /></Row>
                <p className="note">
                  {activeTiles > 0
                    ? `Drawing from ${activeTiles} active tile${activeTiles > 1 ? "s" : ""} in the bank. Each cell is stretched to fill exactly, so ratios vary per cell.`
                    : "No tiles active in the bank — using this layer's own pattern. Bake tiles to mix multiple sources."}
                </p>
              </>)}
            </>)}

            {L && tab === "Place" && (<>
              <Row label="X %"><Slider v={L.x} set={(v) => up({ x: v })} min={-100} max={200} /></Row>
              <Row label="Y %"><Slider v={L.y} set={(v) => up({ y: v })} min={-100} max={200} /></Row>
              <Row label="Width %"><Slider v={L.w} set={(v) => up({ w: v })} min={5} max={300} /></Row>
              <Row label="Height %"><Slider v={L.h} set={(v) => up({ h: v })} min={5} max={300} /></Row>
              <Row label="Rotate"><Slider v={L.rot} set={(v) => up({ rot: v })} min={-180} max={180} /></Row>
              <Row label="Skew"><Slider v={L.skew} set={(v) => up({ skew: v })} min={-45} max={45} /></Row>
              <div className="stack">
                <Toggle v={L.flipX} set={(v) => up({ flipX: v })} label="Flip X" />
                <Toggle v={L.flipY} set={(v) => up({ flipY: v })} label="Flip Y" />
                <Act onClick={() => up({ rot: Math.round(L.rot / 90) * 90 })} icon={Ico.snap} label="Snap 90" />
                <Act onClick={() => up({ x: 0, y: 0, w: 100, h: 100, rot: 0, skew: 0 })} icon={Ico.reset} label="Reset" />
              </div>
            </>)}

            {L && tab === "Layer" && (<>
              <Row label="Name"><input className="text-in" value={L.name} onChange={(e) => up({ name: e.target.value })} /></Row>
              <Row label="Role"><Sel v={L.role} set={(v) => up({ role: v })} opts={["paint", "mask"]} /></Row>
              {L.role === "mask" ? (<>
                <div className="stack"><Toggle v={L.maskInvert} set={(v) => up({ maskInvert: v })} label="Invert mask" /></div>
                <p className="note">Masks the nearest paint layer beneath it by luminance. White keeps, black cuts.</p>
              </>) : (<>
                <Row label="Blend"><Sel v={L.blend} set={(v) => up({ blend: v })} opts={BLENDS} /></Row>
                <Row label="Opacity"><Slider v={L.opacity} set={(v) => up({ opacity: v })} min={0} max={1} step={0.01} /></Row>
              </>)}
              <div className="stack">
                <Act onClick={bakeTile} icon={Ico.bake} label="Bake to tile" />
                <Toggle v={expand} set={setExpand} label="Expand on export" />
              </div>
              <p className="note">Illustrator strips blend modes on SVG import. Reapply them to the named layer groups after placing.</p>
            </>)}

            {tab === "Looks" && (<>
              <Row label="Name">
                <input className="text-in" value={lookName} placeholder={`Look ${looks.length + 1}`}
                  onChange={(e) => setLookName(e.target.value)}
                  onKeyDown={(e) => { if (e.key === "Enter") saveLook(); }} />
              </Row>
              <div className="stack" style={{ paddingTop: 6, paddingBottom: 10 }}>
                <Act onClick={saveLook} icon={Ico.save} label="Save current look" hero />
              </div>

              {looks.length === 0 ? (
                <p className="empty">
                  Saving stores the whole document — every layer, every tile, canvas size and
                  background — as a compact code. Click a thumbnail to restore it exactly.
                </p>
              ) : (
                <div className="lookgrid">
                  {looks.map((lk) => (
                    <div key={lk.id} className="lookcard">
                      <div className="thumb" title={`Load "${lk.name}"`}
                        onClick={() => applyLook(lk.code, `Loaded "${lk.name}"`)}
                        dangerouslySetInnerHTML={{ __html: lookThumb(lk.code) }} />
                      <div className="bar2">
                        <span title={lk.name}>{lk.name}</span>
                        <button className="iconbtn" onClick={() => copyLook(lk.code)} title="Copy code">{Ico.copy}</button>
                        <button className="iconbtn" onClick={() => delLook(lk.id)} title="Delete look">{Ico.trash}</button>
                      </div>
                    </div>
                  ))}
                </div>
              )}

              <div className="sect">Copy out / paste in</div>
              <div className="stack" style={{ paddingTop: 0 }}>
                <Act onClick={() => copyLook(encodeLook(doc))} icon={Ico.copy} label="Copy current as code" />
              </div>
              <textarea className="codebox" style={{ marginTop: 8 }} spellCheck={false}
                placeholder="Paste a look code here…" value={importCode}
                onChange={(e) => setImportCode(e.target.value)} />
              <div className="stack" style={{ paddingTop: 6 }}>
                <Act onClick={doImport} icon={Ico.open} label="Import code" />
              </div>
              <p className="note">
                Codes are plain JSON storing only what differs from the defaults, so they stay short
                enough to paste anywhere.
              </p>
            </>)}

            {tab === "Tiles" && (<>
              <div className="stack" style={{ paddingTop: 0, paddingBottom: 10 }}>
                <Act onClick={bakeTile} icon={Ico.bake} label="Bake current layer" hero />
                {tiles.length > 0 && <Act onClick={() => setTiles([])} icon={Ico.trash} label="Clear" />}
              </div>
              {tiles.length === 0 ? (
                <p className="empty">
                  Bake a layer's pattern here to reuse it as a source tile. Any layer set to <b>collage</b> mode
                  packs the canvas with the active tiles, stretching each to fill its own cell — so one tile
                  can appear at several different ratios in the same sheet.
                </p>
              ) : (
                <div className="tilegrid">
                  {tiles.map((t) => (
                    <div key={t.id} className={`tilecard${t.on ? " on" : ""}`}>
                      <div className="thumb" style={{ opacity: t.on ? 1 : 0.35 }}
                        dangerouslySetInnerHTML={{ __html: tilePreviewSVG(t.params) }} />
                      <div className="bar2">
                        <button className="iconbtn" onClick={() => toggleTile(t.id)} title={t.on ? "Exclude from collage" : "Include in collage"}
                          style={{ color: t.on ? "var(--t0)" : "#3d3d3d" }}>
                          {t.on ? Ico.eye : Ico.eyeOff}
                        </button>
                        <span>{t.name}</span>
                        <button className="iconbtn" onClick={() => delTile(t.id)} title="Delete tile">{Ico.trash}</button>
                      </div>
                    </div>
                  ))}
                </div>
              )}
            </>)}
          </div>

          <div className="layers">
            <div className="layershead">
              <span className="title">Layers</span>
              <button className="iconbtn" onClick={addLayer} title="Add layer">{Ico.add}</button>
              <button className="iconbtn" onClick={dupLayer} title="Duplicate layer">{Ico.copy}</button>
              <button className="iconbtn" onClick={() => move(1)} title="Bring forward">{Ico.up}</button>
              <button className="iconbtn" onClick={() => move(-1)} title="Send backward">{Ico.down}</button>
              <button className="iconbtn" onClick={delLayer} title="Delete layer">{Ico.trash}</button>
            </div>
            <div className="layerlist scroll">
              {[...layers].reverse().map((l) => (
                <div key={l.id} className={`layeritem${l.id === sel ? " on" : ""}`} onClick={() => setSel(l.id)}>
                  <button className={`vis${l.visible ? "" : " off"}`}
                    onClick={(e) => { e.stopPropagation(); setLayers((ls) => ls.map((x) => x.id === l.id ? { ...x, visible: !x.visible } : x)); }}
                    title={l.visible ? "Hide layer" : "Show layer"}>
                    {l.visible ? Ico.eye : Ico.eyeOff}
                  </button>
                  <span className="nm">{l.name}</span>
                  <span className="md">{l.role === "mask" ? "mask" : `${l.mode === "collage" ? "col " : ""}${l.blend.slice(0, 4)}`}</span>
                </div>
              ))}
            </div>
          </div>
        </div>

        <div className="stage" ref={stageRef}>
          <Artboard svg={svg} w={fit.w} h={fit.h} />
          <div className={`toast${msg ? " on" : ""}`}>{msg}</div>
          <div className="readout">
            {W}×{H} · {layers.filter((l) => l.visible).length}/{layers.length} layers · {tiles.length} tiles · {rectCount.toLocaleString()} shapes
          </div>

          {drawer && (
            <div className="drawer">
              <div className="drawerhead">
                <span className="title">{drawer === "png" ? "PNG export" : drawer === "svg" ? "SVG export" : "Preset"}</span>
                {drawer !== "png" && (
                  <Act onClick={async () => flash((await copyText(drawerText)) ? "Copied" : "Clipboard blocked — select and copy")} icon={Ico.copy} label="Copy" />
                )}
                <button className="iconbtn" onClick={() => setDrawer(null)} title="Close">{Ico.close}</button>
              </div>
              <div className="drawerbody">
                <p className="note" style={{ margin: 0 }}>
                  {drawer === "png"
                    ? "A download was attempted. If nothing saved, right-click the image and choose Save image as."
                    : "A download was attempted. If nothing saved, copy the source below and paste straight into Illustrator."}
                </p>
                {drawer === "png" ? (
                  <div className="pngbox">
                    {png === null && <span className="note">Rendering…</span>}
                    {png === "error" && <span className="note" style={{ padding: "0 24px", textAlign: "center" }}>This browser blocked canvas export. Use SVG, or run the tool locally.</span>}
                    {png && png !== "error" && <img src={png} alt="PNG export preview" />}
                  </div>
                ) : (
                  <textarea className="src" readOnly value={drawerText} spellCheck={false} onFocus={(e) => e.target.select()} />
                )}
              </div>
            </div>
          )}
        </div>
      </div>
    </div>
  );
}
