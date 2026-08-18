import React, { useState, useMemo, useRef, useCallback, useEffect, useReducer, useDeferredValue } from "react";

/* ============================================================
   Visual Loom v1.6
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

/* Stops as data, so the same definition feeds both the canvas preview and
   the SVG export. */
function rampStopList(ramp, p, invert) {
  const f = (v) => (invert ? 1 - v : v);
  let pts = [];
  if (ramp === "linear") pts = [[0, 0], [1, 1]];
  else if (ramp === "gamma") { const g = Math.max(0.15, p); for (let i = 0; i <= 10; i++) pts.push([i / 10, Math.pow(i / 10, g)]); }
  else if (ramp === "triangle") pts = [[0, 0], [0.5, 1], [1, 0]];
  else if (ramp === "sine") { for (let i = 0; i <= 12; i++) pts.push([i / 12, (1 - Math.cos(Math.PI * (i / 12))) / 2]); }
  else { const n = Math.max(2, Math.round(p)); for (let i = 0; i < n; i++) { const v = i / (n - 1); pts.push([i / n, v], [(i + 1) / n, v]); } }
  return pts.map(([o, v]) => [o, Math.max(0, Math.min(255, Math.round(f(v) * 255)))]);
}
const greyHex = (c) => { const h = c.toString(16).padStart(2, "0"); return `#${h}${h}${h}`; };
const rampStops = (ramp, p, invert) =>
  rampStopList(ramp, p, invert).map(([o, c]) => `<stop offset="${+o.toFixed(4)}" stop-color="${greyHex(c)}"/>`).join("");

const gradId = (ramp, p, dir, invert) =>
  `g_${ramp}_${String(+p.toFixed(2)).replace(".", "-")}_${dir}${invert ? "_i" : ""}`;

/* every distinct gradient used anywhere, keyed by id */
const GRADS = new Map();
function gradRef(ramp, p, dir, invert) {
  const id = gradId(ramp, p, dir, invert);
  if (!GRADS.has(id)) GRADS.set(id, { id, ramp, p, dir, invert, stops: rampStopList(ramp, p, invert) });
  return id;
}
const gradDefs = (ids) => [...ids].map((id) => {
  const g = GRADS.get(id);
  const [x1, y1, x2, y2] = DIRS[g.dir];
  return `<linearGradient id="${g.id}" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}">${rampStops(g.ramp, g.p, g.invert)}</linearGradient>`;
}).join("");

/* ---- affine matrices, shared by canvas and SVG ---- */
const mMul = (m, n) => [
  m[0] * n[0] + m[2] * n[1], m[1] * n[0] + m[3] * n[1],
  m[0] * n[2] + m[2] * n[3], m[1] * n[2] + m[3] * n[3],
  m[0] * n[4] + m[2] * n[5] + m[4], m[1] * n[4] + m[3] * n[5] + m[5],
];
const mT = (x, y) => [1, 0, 0, 1, x, y];
const mS = (x, y) => [x, 0, 0, y, 0, 0];
const mR = (d) => { const a = d * Math.PI / 180, c = Math.cos(a), s = Math.sin(a); return [c, s, -s, c, 0, 0]; };
const mSkewX = (d) => [1, 0, Math.tan(d * Math.PI / 180), 1, 0, 0];
const mChain = (...ms) => ms.reduce(mMul);
const mStr = (m) => `matrix(${m.map((v) => +v.toFixed(5)).join(" ")})`;

/* ---------------- tile geometry ---------------- */
const U = 1000;
const GEN_KEYS = ["seed", "cols", "rows", "colMode", "rowMode", "stripeMode", "freqMin", "freqMax",
  "freqMapX", "freqMapY", "axisBias", "invertChance", "voidChance", "rampMode", "gamma", "stepMax", "pingPong"];
const genParams = (L) => Object.fromEntries(GEN_KEYS.map((k) => [k, L[k]]));
const tileKey = (P) => GEN_KEYS.map((k) => P[k]).join("|");

/* Rects as plain numbers rather than markup — the canvas draws them directly
   and the SVG exporter formats them only when exporting. */
function buildTile(P) {
  const r = mulberry32(P.seed >>> 0);
  const cols = toOffsets(makeWeights(P.cols, P.colMode, r), U);
  const rows = toOffsets(makeWeights(P.rows, P.rowMode, r), U);
  const rects = [], grads = new Set();
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
      sw.forEach((sg, si) => {
        const flip = P.pingPong ? (baseFlip !== (si % 2 === 1)) : baseFlip;
        const dir = axis === "x" ? (flip ? "l" : "r") : (flip ? "u" : "d");
        const g = gradRef(ramp, p, dir, cellInvert);
        grads.add(g);
        rects.push({
          x: axis === "x" ? co.pos + sg.pos : co.pos,
          y: axis === "x" ? ro.pos : ro.pos + sg.pos,
          w: (axis === "x" ? sg.size : co.size) + 0.4,
          h: (axis === "x" ? ro.size : sg.size) + 0.4,
          g,
        });
      });
    });
  });
  return { rects, grads: [...grads] };
}

const TILE_CACHE = new Map();
const TILE_CACHE_MAX = 300;
function tileGeom(P) {
  const k = tileKey(P);
  let e = TILE_CACHE.get(k);
  if (!e) {
    e = buildTile(P);
    TILE_CACHE.set(k, e);
    if (TILE_CACHE.size > TILE_CACHE_MAX) TILE_CACHE.delete(TILE_CACHE.keys().next().value);
  }
  return e;
}

/* ---------------- packing ---------------- */
function repeatCells(L, r) {
  const cw = toOffsets(makeWeights(Math.max(1, L.tileX | 0), L.tileMode, r), U);
  const ch = toOffsets(makeWeights(Math.max(1, L.tileY | 0), L.tileMode, r), U);
  const out = [];
  ch.forEach((rr) => cw.forEach((cc) => out.push({ x: cc.pos, y: rr.pos, w: cc.size, h: rr.size })));
  return out;
}

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

/* instances: which tile goes in which cell, and the matrix that places it */
function layerInstances(L, tiles, used) {
  const r = mulberry32((L.seed ^ 0x9e3779b9) >>> 0);
  const collage = L.mode === "collage";
  const cells = collage ? collageCells(L, r) : repeatCells(L, r);
  const active = tiles.filter((t) => t.on);
  const pool = collage && active.length ? active.map((t) => t.params) : [genParams(L)];
  const gap = collage ? L.gap : 0;

  return cells.map((c) => {
    const P = pool.length === 1 ? pool[0] : pick(pool, r);
    const k = tileKey(P);
    if (!used.has(k)) used.set(k, P);
    const rotate = collage ? (r() < L.rotChance ? pick([90, 180, 270], r) : 0)
      : (L.tileRot ? pick([0, 90, 180, 270], r) : 0);
    const fx = (collage ? r() < L.flipChance : L.tileFlip && r() < 0.5) ? -1 : 1;
    const fy = (collage ? r() < L.flipChance : L.tileFlip && r() < 0.5) ? -1 : 1;
    const w = Math.max(1, c.w - gap), h = Math.max(1, c.h - gap);
    return {
      tile: k,
      m: mChain(mT(c.x + c.w / 2, c.y + c.h / 2), mS(fx * w / U, fy * h / U), mR(rotate), mT(-U / 2, -U / 2)),
    };
  });
}

/* Layers live in a square master the size of the canvas's longer edge, centred.
   1:1 shows all of it; every other ratio is a crop of the same artwork. */
function layerMatrix(L, W, H) {
  const M = Math.max(W, H);
  const ox = (W - M) / 2, oy = (H - M) / 2;
  const bw = (L.w / 100) * M, bh = (L.h / 100) * M;
  const cx = ox + (L.x / 100) * M + bw / 2, cy = oy + (L.y / 100) * M + bh / 2;
  return mChain(
    mT(cx, cy),
    L.rot ? mR(L.rot) : [1, 0, 0, 1, 0, 0],
    L.skew ? mSkewX(L.skew) : [1, 0, 0, 1, 0, 0],
    mS((L.flipX ? -1 : 1) * bw / U, (L.flipY ? -1 : 1) * bh / U),
    mT(-U / 2, -U / 2),
  );
}

/* ---------------- model ---------------- */
/* Drift: a live offset layered on top of each layer's stored placement.
   Each layer responds at a different rate, so sliding them across one another
   shifts the interference pattern continuously. Matrix-only — no geometry is
   rebuilt, so it stays at frame rate on any stack. */
function driftLayer(L, d, i, n) {
  if (!d) return L;
  /* front layers move most, back layers barely — that spread is the effect */
  const f = n < 2 ? 1 : 0.25 + 0.75 * (i / (n - 1));
  const sc = 1 + (d.dy || 0) * 0.55 * f;
  /* deliberately unbounded: layers are free to travel past the frame.
     The only guard is against a degenerate zero-scale matrix. */
  return {
    ...L,
    x: L.x + (d.dx || 0) * 45 * f,
    rot: L.rot + (d.rx || 0) * 60 * f,
    w: Math.max(1, L.w * sc),
    h: Math.max(1, L.h * sc),
  };
}

function buildModel(doc) {
  const { W, H, layers, bg, tiles, drift } = doc;
  const vis = layers.filter((L) => L.visible);
  const used = new Map();
  const built = vis.map((L0, i) => {
    const L = driftLayer(L0, drift, i, vis.length);
    return { L, m: layerMatrix(L, W, H), inst: layerInstances(L, tiles, used) };
  });

  /* a mask layer applies to the nearest paint layer beneath it */
  const out = [];
  built.forEach((b, i) => {
    if (b.L.role !== "mask") { out.push(b); return; }
    for (let j = i - 1; j >= 0; j--) {
      if (built[j].L.role === "paint") { built[j].mask = b; break; }
    }
  });

  const tileList = [...used.entries()].map(([k, P]) => ({ key: k, ...tileGeom(P) }));
  const gradIds = new Set();
  tileList.forEach((t) => t.grads.forEach((g) => gradIds.add(g)));

  return { W, H, bg, tiles: tileList, gradIds, layers: out };
}

/* ---------------- SVG export ---------------- */
const rectStr = (r) =>
  `<rect x="${+r.x.toFixed(2)}" y="${+r.y.toFixed(2)}" width="${+r.w.toFixed(2)}" height="${+r.h.toFixed(2)}" fill="url(#${r.g})"/>`;

function modelToSVG(m, expand) {
  const tileMarkup = new Map(m.tiles.map((t) => [t.key, t.rects.map(rectStr).join("")]));
  const body = (b) => b.inst.map((it) => expand
    ? `<g transform="${mStr(it.m)}">${tileMarkup.get(it.tile)}</g>`
    : `<g transform="${mStr(it.m)}"><use href="#t_${m.tiles.findIndex((t) => t.key === it.tile)}"/></g>`).join("");

  const masks = [];
  const groups = m.layers.map((b) => {
    let maskAttr = "";
    if (b.mask) {
      const id = `m_${b.mask.L.id}`;
      masks.push(`<mask id="${id}" maskUnits="userSpaceOnUse" x="0" y="0" width="${m.W}" height="${m.H}" style="mask-type:luminance">` +
        `<rect x="0" y="0" width="${m.W}" height="${m.H}" fill="${b.mask.L.maskInvert ? "#fff" : "#000"}"/>` +
        `<g${b.mask.L.maskInvert ? ' style="mix-blend-mode:difference"' : ""}><g transform="${mStr(b.mask.m)}">${body(b.mask)}</g></g></mask>`);
      maskAttr = ` mask="url(#${id})"`;
    }
    return `<g id="${b.L.name.replace(/[^\w-]/g, "_")}" style="mix-blend-mode:${b.L.blend};opacity:${b.L.opacity}"${maskAttr}>` +
      `<g transform="${mStr(b.m)}">${body(b)}</g></g>`;
  }).join("");

  const symbols = expand ? "" : m.tiles.map((t, i) => `<g id="t_${i}">${tileMarkup.get(t.key)}</g>`).join("");
  return `<svg xmlns="http://www.w3.org/2000/svg" width="${m.W}" height="${m.H}" viewBox="0 0 ${m.W} ${m.H}">` +
    `<defs>${gradDefs(m.gradIds)}${symbols}${masks.join("")}</defs>` +
    (m.bg !== "none" ? `<rect x="0" y="0" width="${m.W}" height="${m.H}" fill="${m.bg}"/>` : "") +
    `<g style="isolation:isolate">${groups}</g></svg>`;
}
const buildSVG = (doc, expand = false) => modelToSVG(buildModel(doc), expand);

const TILE_THUMBS = new Map();
function tilePreviewSVG(P) {
  const k = tileKey(P);
  if (TILE_THUMBS.has(k)) return TILE_THUMBS.get(k);
  const { rects, grads } = tileGeom(P);
  const out = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${U} ${U}" width="100%" height="100%" preserveAspectRatio="none">` +
    `<defs>${gradDefs(grads)}</defs><rect width="${U}" height="${U}" fill="#fff"/>${rects.map(rectStr).join("")}</svg>`;
  TILE_THUMBS.set(k, out);
  return out;
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
/* every preset shares a 3840px long edge, so switching ratio only changes
   which part of the same square master is visible */
const SIZES = [["1:1", 3840, 3840], ["16:9", 3840, 2160], ["9:16", 2160, 3840],
["4:5", 3072, 3840], ["4:3", 3840, 2880], ["3:1", 3840, 1280]];
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

/* Layer count comes from the user's range, so the strategy is picked to suit
   that depth: shallow stacks get heavy grain, deep stacks get finer grain. */
function strategyFor(n, r) {
  if (n <= 2) return pick(["chunky", "chunky", "chunky", "contrast", "contrast", "medium"], r);
  if (n === 3) return pick(["chunky", "chunky", "contrast", "contrast", "contrast", "graded", "medium"], r);
  if (n === 4) return pick(["contrast", "contrast", "chunky", "graded", "graded", "medium", "fine"], r);
  if (n <= 7) return pick(["fine", "fine", "contrast", "graded", "graded", "medium"], r);
  /* 8+ layers: heavy grain reads, fine grain stacks into noise */
  return pick(["chunky", "chunky", "contrast", "contrast", "graded", "medium"], r);
}

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

/* The identity sits on its own line so the toolbar gets the full width and
   starts at the left edge. */
/* Identity sits at the foot of the rail, rotated so its top edge faces the
   left screen edge. Absolutely positioned so the rotation doesn't reserve
   horizontal space the rail can't give. */
.pd .railfoot { flex:1; min-height:0; width:100%; position:relative; }
.pd .railmark { position:absolute; left:50%; bottom:18px; margin-left:-8px;
  transform-origin:0 0; transform:rotate(-90deg);
  display:flex; align-items:center; gap:9px; white-space:nowrap; }
.pd .railmark .brand { font-size:10px; letter-spacing:.22em; }
.pd .railmark .ver { font-size:9px; }

/* ONE row, fixed height. It collapses at CSS breakpoints rather than by
   measurement, so it can never be clipped, wrap, or get stuck at the wrong
   size when the window is resized. */
.pd .top { flex:none; height:44px; display:flex; flex-wrap:nowrap; align-items:center;
  gap:8px; padding:0 12px; border-bottom:1px solid var(--bd2); overflow:visible; min-width:0; }
.pd .helpbtn { margin-left:2px; }

/* under 1700: secondary buttons drop to icons, swatches lose their names */
@media (max-width:1700px) {
  .pd .top .btn:not(.hero) span { display:none; }
  .pd .top .btn:not(.hero) { padding:0 7px; gap:0; }
  .pd .top .sw span { display:none; }
  .pd .top .sw { padding:0 6px; }
  .pd .top .glabel { display:none; }
  .pd .top .rangefield .cap { display:none; }
  .pd .top .rangefield { padding:0 6px; }
  .pd .top { gap:6px; }
}
/* under 1180: explicit pixel dimensions go, aspect presets remain */
@media (max-width:1180px) {
  .pd .top .dims { display:none; }
}
/* under 940: last resort, the row scrolls rather than clipping */
@media (max-width:940px) {
  .pd .top { overflow-x:auto; scrollbar-width:none; }
  .pd .top::-webkit-scrollbar { display:none; }
}

.pd .sizechips { display:flex; gap:3px; }
.pd .dims { display:flex; align-items:center; gap:5px; }
.pd .dims .x { color:var(--t2); font-size:10px; }
.pd .grounds { display:flex; align-items:center; gap:4px; }
.pd .grounds .glabel { color:var(--t1); white-space:nowrap; }

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
.pd .btn.glow { border-color:#7b3fd4; color:#fff;
  box-shadow:0 0 0 1px rgba(123,63,212,.5), 0 0 14px 2px rgba(123,63,212,.55);
  animation:pdglow 2.4s ease-in-out infinite; }
.pd .btn.glow:hover { border-color:#9d6bf0;
  box-shadow:0 0 0 1px rgba(157,107,240,.7), 0 0 20px 4px rgba(123,63,212,.8); }
@keyframes pdglow {
  0%, 100% { box-shadow:0 0 0 1px rgba(123,63,212,.45), 0 0 10px 1px rgba(123,63,212,.4); }
  50%      { box-shadow:0 0 0 1px rgba(123,63,212,.7), 0 0 20px 4px rgba(123,63,212,.75); }
}
@media (prefers-reduced-motion: reduce) { .pd .btn.glow { animation:none; } }
.pd .btn.hero { border-color:#7a7a7a; color:var(--t0); }
.pd .btn.hero:hover { background:var(--s2); border-color:var(--bd3); }
.pd .chip { height:28px; padding:0 8px; border:1px solid var(--bd2); color:var(--t2);
  font-size:10px; font-family:ui-monospace,monospace; }
.pd .chip:hover { border-color:#5c5c5c; }
.pd .chip.on { border-color:var(--bd3); color:var(--t0); background:var(--s2); }
.pd .iconbtn { color:var(--t1); display:inline-flex; align-items:center; }
.pd .iconbtn:hover { color:var(--t0); }

.pd .rangefield { display:flex; align-items:center; gap:5px; height:28px; padding:0 8px;
  border:1px solid var(--bd2); }
.pd .rangefield .cap { color:var(--t2); }
.pd .rangefield .dash { color:var(--t2); font-size:10px; }
.pd .mini { width:30px; height:20px; padding:0 3px; background:var(--s1); border:1px solid var(--bd);
  color:var(--t0); font-size:10px; font-family:ui-monospace,monospace; text-align:center; outline:none; }
.pd .mini:focus { border-color:#8a8a8a; }
.pd .mini::-webkit-outer-spin-button, .pd .mini::-webkit-inner-spin-button { -webkit-appearance:none; margin:0; }
.pd .mini { -moz-appearance:textfield; }
/* The wrapper's hover area has to span the button AND the menu, otherwise
   crossing the gap between them fires mouseleave and the menu closes before
   it can be clicked. A pseudo-element bridges the gap. */
.pd .menuwrap { position:relative; display:inline-flex; }
/* invisible bridge across the gap so travelling to the menu can't dismiss it */
.pd .popmenu::before { content:""; position:absolute; left:0; right:0; bottom:100%; height:10px; }
.pd .popmenu { position:fixed; z-index:200; min-width:172px; display:flex; flex-direction:column;
  background:var(--s2); border:1px solid var(--bd); box-shadow:0 8px 24px rgba(0,0,0,.6); }
.pd .popmenu button { display:flex; align-items:center; justify-content:space-between; gap:12px;
  padding:6px 10px; text-align:left; }
.pd .popmenu button:hover { background:#2a2a2a; }
.pd .popmenu button > span { font-size:9.5px; letter-spacing:.1em; text-transform:uppercase; color:var(--t0); }
.pd .popmenu em { font-style:normal; font-size:9px; font-family:ui-monospace,monospace; color:var(--t2); }
.pd .popmenu .menuhead { padding:6px 10px 4px; font-size:8.5px; letter-spacing:.18em;
  text-transform:uppercase; color:var(--t2); border-bottom:1px solid var(--bd2); }
.pd .popmenu button.on { background:rgba(123,63,212,.15); }
.pd .popmenu button.on > span { color:#c9a4ff; }
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
.pd .body { flex:1; min-height:120px; padding:10px 12px; overflow-x:visible; }

.pd .row { display:flex; align-items:center; gap:10px; height:30px; }
.pd .tip { position:absolute; left:0; bottom:calc(100% + 6px); z-index:40; width:210px;
  padding:7px 9px; background:#1c1c1c; border:1px solid #4a4a4a; color:var(--t0);
  font-size:10px; line-height:1.45; letter-spacing:0; text-transform:none; font-weight:400;
  opacity:0; visibility:hidden; transition:opacity .12s ease .25s, visibility 0s linear .37s;
  pointer-events:none; box-shadow:0 6px 18px rgba(0,0,0,.55); }
.pd .lab.tipped { position:relative; cursor:help; }
.pd .lab.tipped:hover { color:var(--t0); }
.pd .lab.tipped:hover .tip { opacity:1; visibility:visible; transition-delay:.25s, .25s; }
.pd .row > .lab { flex:none; width:80px; font-size:9.5px; letter-spacing:.08em; text-transform:uppercase;
  color:var(--t1); white-space:nowrap; }
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

.pd .layers { flex:none; border-top:1px solid var(--bd2); display:flex; flex-direction:column; min-height:0; }
.pd .layershead { height:30px; display:flex; align-items:center; gap:10px; padding:0 12px; }
.pd .layershead .title { font-size:9.5px; font-weight:500; letter-spacing:.18em; text-transform:uppercase;
  color:var(--t1); margin-right:auto; }
.pd .layerlist { max-height:352px; padding-bottom:4px; }
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

.pd .stage { flex:1; min-width:0; min-height:0; position:relative; touch-action:none; display:flex; align-items:center;
  justify-content:center; background:var(--s1); overflow:hidden; }
.pd .art { position:relative; border:1px solid #3a3a3a; overflow:hidden; }
.pd .art > div { position:absolute; inset:0; }
.pd .toast { position:absolute; right:12px; bottom:8px; padding:5px 9px; pointer-events:none;
  background:rgba(11,11,11,.88); border:1px solid var(--bd2); color:var(--t1);
  font-size:9.5px; font-family:ui-monospace,monospace; opacity:0; transition:opacity .16s ease; }
.pd .toast.on { opacity:1; }
.pd .empty-stage { width:100%; height:100%; display:flex; flex-direction:column;
  align-items:center; justify-content:center; gap:22px; padding:0 32px; text-align:center; }
.pd .empty-stage .lead { max-width:430px; margin:0; font-size:12.5px; line-height:1.75;
  color:var(--t1); letter-spacing:.01em; }
.pd .empty-stage .cta { margin:0; display:flex; align-items:center; gap:8px;
  font-size:10px; font-weight:600; letter-spacing:.2em; text-transform:uppercase; color:#a97cf0; }
.pd .empty-stage kbd { display:inline-flex; align-items:center; padding:4px 12px;
  border:1px solid rgba(169,124,240,.55); background:rgba(123,63,212,.14); color:#c9a4ff;
  font:inherit; letter-spacing:.16em; }
.pd .empty-stage .alt { margin:-10px 0 0; font-size:10px; letter-spacing:.06em; color:var(--t2); }

/* coach mark: sits under the Random Look button and points back up at it */
.pd .coachwrap { position:relative; display:inline-flex; }
.pd .coach { position:absolute; top:calc(100% + 9px); left:50%; z-index:50;
  transform:translateX(-50%); padding:5px 11px; white-space:nowrap;
  background:#7b3fd4; color:#fff; font-size:9.5px; font-weight:600;
  letter-spacing:.14em; text-transform:uppercase; pointer-events:none;
  box-shadow:0 4px 16px rgba(123,63,212,.5);
  animation:pdcoach 1.9s ease-in-out infinite; }
.pd .coach .arrow { position:absolute; bottom:100%; left:50%; margin-left:-5px;
  border-left:5px solid transparent; border-right:5px solid transparent;
  border-bottom:5px solid #7b3fd4; }
@keyframes pdcoach {
  0%, 100% { transform:translateX(-50%) translateY(0); }
  50%      { transform:translateX(-50%) translateY(4px); }
}
@media (prefers-reduced-motion: reduce) { .pd .coach { animation:none; } }

.pd .help { position:absolute; inset:0; background:rgba(11,11,11,.97); display:flex;
  flex-direction:column; z-index:60; }
.pd .helphead { flex:none; height:40px; display:flex; align-items:center; gap:10px;
  padding:0 16px; border-bottom:1px solid var(--bd2); }
.pd .helphead .title { font-size:10px; font-weight:600; letter-spacing:.2em;
  text-transform:uppercase; margin-right:auto; }
.pd .helpbody { flex:1; min-height:0; overflow-y:auto; padding:20px 24px 28px;
  scrollbar-width:none; }
.pd .helpbody::-webkit-scrollbar { display:none; }
.pd .helpbody .wrap { max-width:560px; margin:0 auto; }
.pd .helpbody h4 { font-size:9.5px; font-weight:600; letter-spacing:.2em; text-transform:uppercase;
  color:var(--t2); margin:22px 0 8px; padding-bottom:5px; border-bottom:1px solid var(--bd2); }
.pd .helpbody h4:first-child { margin-top:0; }
.pd .helpbody p { margin:0 0 9px; font-size:11.5px; line-height:1.65; color:var(--t1); }
.pd .helpbody b { color:var(--t0); font-weight:500; }
.pd .helpbody dl { margin:0; display:grid; grid-template-columns:74px 1fr; gap:7px 14px; }
.pd .helpbody dt { font-size:9.5px; letter-spacing:.1em; text-transform:uppercase; color:var(--t0);
  padding-top:2px; }
.pd .helpbody dd { margin:0; font-size:11.5px; line-height:1.55; color:var(--t1); }
.pd .drifthint { position:absolute; right:12px; top:10px; display:flex; align-items:center; gap:8px;
  font-size:9px; font-family:ui-monospace,monospace; color:var(--t2); user-select:none; }
.pd .drifthint span { opacity:.75; }
.pd .stepbtn { padding:3px 7px; border:1px solid var(--bd2); color:var(--t2);
  font-size:8.5px; letter-spacing:.1em; text-transform:uppercase; pointer-events:auto; }
.pd .stepbtn:hover { border-color:#5c5c5c; color:var(--t0); }
.pd .stepbtn.on { border-color:#7b3fd4; color:#c9a4ff; background:rgba(123,63,212,.16); }
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

/* Prismdrifter lockup — wide wordmark, inherits colour from surrounding text */
const LOGO_RATIO = 10.0047;
const Mark = ({ h = 16 }) => (
  <svg height={h} width={Math.round(h * LOGO_RATIO)} viewBox="0 0 1080 107.9493671" fill="currentColor"
    xmlns="http://www.w3.org/2000/svg" aria-label="Prismdrifter" style={{ flex: "none", display: "block" }}>
    <path d="M659.8234196,38.004383c-.1592684,14.0537835.5318129,32.4471239-.5087707,45.3895224-2.5378851,10.2761266-10.0677941-12.684-8.5720157-16.0001441.1664183-7.7280889,4.3587838-13.8006888,6.1298454-21.7413441,2.8451003-11.9879066-3.1889729-25.1475153-14.1772487-30.7057033-14.0080469-7.0884136-35.7711978-3.4219899-52.5974477-4.3127227-9.3904781.9287358-23.5776097-2.8242498-30.0388698,4.2437976-3.0553237,4.0612848-2.5459728,10.0133986-4.4610082,13.3666991-3.2306863,4.1133745-10.1214536-5.2803823-13.6899893-7.0395189-4.21827-3.0913813-9.071179-5.3580852-14.0600045-6.9187128-17.6893963-5.4208495-40.1806345-3.146867-58.4317677-3.6517784-13.9337357.2336713-28.8783272-.5536391-42.6460759.4747716-21.2553676,1.0661104-17.6582131,29.4342466-28.5610833,40.8867128-7.9776145-.5410525-9.8041047-31.5670448-19.4580087-37.2343855-5.2564935-4.1266191-12.5209408-3.9730823-18.979027-4.1122651-10.5860142.0067037-23.0181797-1.0867541-26.2748212,10.5962728-2.4802706,13.7337444-9.6401387-6.881003-29.2580333-9.5952447-17.3125352-3.219925-37.2729401-3.1116839-52.6273594,6.4767905-19.0192957,12.8945311-11.0563087,37.1251918,9.5027457,43.1371734,8.7026464,3.3047325,18.7698293,3.9114655,27.5967143,6.5619797,13.4688572,4.0396895,6.1719228,9.6690538-2.2615575,9.570034-11.2089554-.1772889-21.543372-6.677001-32.3894671-8.6038038-11.8623168-1.8358-16.8460638-6.6171715-16.2546251-19.839506-1.2672716-10.5589228,3.5708675-29.2239158-5.6474358-35.7789065-6.2927109-3.6358261-17.2444906-2.7871154-21.7895183,3.8601353-3.4757457,4.8329752-3.2385247,11.5556465-3.2564289,18.9948531-.0000347,8.077332-.000005,16.3950167-.0000149,26.5463.1319833,9.8657776,1.1646626,40.0048239-8.4082919,11.9435449-2.727065-10.2440383,2.8092239-18.821428,5.3922363-28.5691804,3.3906166-13.2560889-4.4068168-27.6925049-17.1540488-32.4269459-11.002-4.3723355-29.07407-2.4660587-42.7356432-2.8882398-11.9455141,1.0546003-28.4318236-3.2546228-37.5930084,4.6811042-7.393673,9.4014892-15.3160627-1.5938636-24.7539885-3.1534799-18.850103-3.0616979-41.159525-1.0073632-59.5818145-1.4367594-10.6354074-.3062242-13.2589176,3.8195829-12.7085164,14.7544729-.0431874,13.6490475-.0153724,38.5164341-.0160936,53.7011423.1608964,5.4182436-.6378111,12.3567753,4.3389283,15.5940475,6.2072632,3.5199109,17.4279806,2.9671026,22.6090175-3.4838036,4.3642014-5.2812457,4.1249339-13.5228132,10.7625319-17.0212278,6.8541085-3.7041225,15.5796946-2.3034366,24.044101-3.0471867,10.0749995.1672982,19.1484768-4.6000283,27.6783273-8.9641348,8.5345799-2.3514453,3.5420127,21.5439516,7.139389,26.7990852,3.1888379,8.6373509,15.8327926,9.8485914,22.8943829,4.5303282,6.3253495-4.6018819,5.5182329-13.8789931,11.2665681-18.9476119,6.2394741-6.0278902,15.2323862-3.4132523,21.4472304,1.9999773,6.4458319,5.6093464,9.7550039,14.4842414,18.0406463,17.9064364,8.8666859,3.9521185,19.9099184,2.3700732,30.0041083,2.7025033,8.7766887.7956312,20.7613705-1.161143,26.6028918-6.815706,7.7630497-6.9421311,16.701811,2.928509,25.0785453,4.5419264,13.9989518,3.8598094,29.3349839,4.1224576,43.4928515,1.4667955,9.9664463-.9691706,19.7304982-11.0876318,29.3907377-5.1232408,32.7182803,18.461063,26.7677011-17.4309024,27.5450975-37.7334475,1.1823763-16.7138056,8.9499388,12.144016,11.1776061,17.4985254,2.9625989,8.1995928,5.1310154,15.6694802,10.7132524,20.7616113,9.0474641,8.447061,23.7443151,4.877455,29.1097349-6.2365041,5.1038758-9.8069384,8.4058996-23.3237731,12.6544059-33.3057188,6.2493461-13.795079,4.2955206,13.5125935,4.5742617,19.0448575-.672662,12.8546735,1.2249764,26.227119,17.1778325,25.7839651,11.1648706.2740942,20.6591515.0449604,32.8550443.1167806,21.9664-.3248474,46.3456582,2.2120213,64.0611656-12.3142992,3.5737821-1.9541044,8.3283263-9.4642865,11.5826706-4.9125506,1.5540535,3.8649936,2.5865762,9.2998772,5.9701273,12.4383956,10.1750848,9.4966002,24.5678982,2.0063613,26.8309025-10.9486223,3.2331263-10.6218949,15.381561-13.4070567,23.9842992-6.3327384,8.3859475,6.0113477,11.7977489,17.5700767,22.5286032,20.3860612,7.5435226,2.4017609,16.8007595,1.5000587,25.3412518,1.683771,8.6764507-.5172543,18.8541922,1.6158077,26.3680843-3.0359469,7.5952006-4.9025801,2.0434592-56.8344806,3.6349819-67.7509476-.0962119-4.5231223.0302719-9.7293223-3.4524351-12.7304666-4.7172853-3.423611-12.8313153-3.5360515-18.3649487-1.1778513-9.9822582,4.6015055-8.6455239,15.0194388-8.811753,25.2928283v.1574437ZM76.0821419,45.4523609c-4.6982406,5.1009864-16.7878251,4.7459299-23.8584151,4.5399457-5.3573831-.3616316-10.5434081-1.7176148-12.7541522-6.2307285-1.2650866-2.7131288-.1637845-5.7598631,2.0621977-7.6438438,4.9232045-4.185162,12.9018122-3.7253874,20.0661319-3.4687396,5.3351162.1157823,13.5359611,1.7993845,15.3206546,5.8216091,1.183861,2.2402641.9430964,4.898162-.7639689,6.8983261l-.0724479.0834309ZM173.0194846,44.1872746c-2.3105345,2.5401046-5.7317984,3.4650189-10.6585396,4.0940388-7.198124.5152278-16.9080414,1.2843542-23.436965-1.3531596-6.9197422-2.9394923-6.8933288-9.5531713-.258035-12.4998923,3.6966735-1.7800086,9.3519374-2.0098857,15.2012686-1.9238174,7.4703288.3335541,14.8248971.0499631,19.2924277,4.7826916,1.6084228,2.0202748,1.6243946,4.7790077-.0739535,6.8207012l-.0662032.0794376ZM326.6767006,53.4070582c-3.568243-1.7094966-8.533385-4.8018089-13.1948978-6.4594706-7.923246-2.9915396-16.3294796-4.3122092-24.6293195-5.8245578-3.1318737-.5852506-6.3040717-1.2593583-9.2702762-2.3337926-8.4164961-2.8794882-10.749597-8.353739-3.3163719-11.4202942,5.0947143-2.1346761,11.4067737-1.3455353,16.4650543.6107401,6.7189493,2.576703,13.0708836,6.1411227,20.2024422,7.5853834,5.7172361,1.3584327,12.4301559,1.2365232,16.8331978,4.1583981,2.5060966,1.6124015,4.5125843,4.2310541,5.2971985,7.0607561,1.5873714,5.9700491-2.2340642,9.9216594-8.2579428,6.6824193l-.1290845-.0595818ZM527.1241373,55.271935c-.9350891,13.1687302-12.2319053,19.4752264-24.3771741,20.0848803-15.2938472,1.3057776-14.4499265-10.1872477-14.416784-21.7972216-.1229401-12.3979108-.2090193-22.5981874,15.5096171-20.9296816,12.9908219.9070212,23.8774774,8.4840291,23.2938523,22.4896243l-.0095113.1523986ZM625.730758,44.1872746c-2.3105345,2.5401046-5.7317984,3.4650189-10.6585396,4.0940388-7.198124.5152278-16.9080414,1.2843542-23.436965-1.3531596-6.9197422-2.9394923-6.8933288-9.5531713-.258035-12.4998923,3.6966735-1.7800086,9.3519374-2.0098857,15.2012686-1.9238174,7.4703288.3335541,14.8248971.0499631,19.2924277,4.7826916,1.6084228,2.0202748,1.6243946,4.7790077-.0739535,6.8207012l-.0662032.0794376Z"/>
    <path d="M1062.5531947,65.5438102c1.0998602-7.5117345,6.5121116-13.6998482,7.5231013-21.3049718,2.3427255-12.4508101-5.2852621-25.4350743-16.7621041-29.863977-7.3755627-3.1667504-15.2954618-3.0011148-23.2617246-3.0936051-45.7872771-.0345216-94.4377784.0060868-139.8490578-.0089796-42.2414052.0048544-88.2481949-.0034345-130.445662.000048-17.1126577.0671392-42.5251976-.1165673-58.9495336.067681-5.1899463.1642362-7.7566799.7511077-8.8172061,3.4473236-.9963438,2.923397-.8864405,6.6700186-.9260815,10.0080556.3376122,17.4167986-.6274158,46.034831.3609293,64.0475881.5963157,4.2760936,2.8389958,6.2333073,7.3103647,7.0728302,5.6645807.921306,12.7948728,1.1099553,17.8279409-2.2342105,6.7438703-4.4242608,4.3000455-14.9397862,7.9200624-20.6067658,4.867166-6.9956342,16.9655802-4.4048854,24.6441843-4.9709752,6.8068439-.1486857,15.2200988.5542537,19.3875374-4.8053038,3.4115293-4.4575529,2.4085831-11.2413637-3.17046-14.2761055-3.059076-1.7122197-7.7545479-2.0809485-13.3110053-2.1197104-8.1944962-.5706329-24.1880186,2.1989243-28.162623-6.4761967-1.3115262-6.67904,12.1897626-8.3206762,18.9017051-7.9296817,6.2557688-.0123048,13.6700859-.0010288,19.6501107-.0048392,9.0853655-.0029434,17.4678007.0020847,26.4531732.0000457,7.823995.1845869,15.1760384-.5459306,19.9817068,2.5585365,3.942325,3.0834808,3.4154695,8.212084,3.6721728,13.0159946.4443418,11.2364478-.9343838,30.4818729.8524013,41.3584627,1.7808751,6.7656265,8.7543784,6.9880146,15.5073766,7.0759426,16.2903601.1474474,14.5355552-8.7995086,14.6306558-22.5285719.0070698-7.9844798-.0129522-16.2948696.0087923-24.2820202.2951058-7.8728303-.3302787-12.478404,4.9406185-15.3813122,6.2515088-2.4328226,18.5363184-2.5950109,24.8121069.2447902,5.1132191,3.3415247,4.1549398,8.1922667,4.4749002,16.4488151.0909605,11.1493792-.1884121,26.008675.1600484,36.3009296.1075407,4.5298323,1.2836633,8.5433262,5.5716374,8.9109314,19.8254358,1.1037384,52.1851904.1080545,70.8008945.432427,7.6509746.0013152,14.8124195-.0019231,22.4473885-.000671,5.273788-.0183585,11.127653.116552,15.4309195-2.0245649,7.4935335-3.2762717,6.3464722-12.6376444,10.1561224-18.5966492,4.8960895-7.1463012,14.9703198-6.7302605,21.9889207-2.0778714,7.2727814,4.4555686,9.4830638,13.7205248,16.3582289,18.555405,6.5622033,4.7322364,21.1495011,5.4876321,27.1192483,1.9558706,5.9554867-4.3213335-7.5174925-18.8964733-5.2539773-28.7855454l.0161861-.1291487ZM910.1290867,71.6020892c-3.3840687-4.5964518,5.1761844-6.8711405,8.561723-7.38637,8.5972169-1.1490914,19.0245623-.2490539,27.4356297-.6971657,3.4555883-.1837702,7.1397218-.5525274,10.0299246-2.4238273,5.712683-3.7556889,5.590584-11.6992319-.3979171-15.2623627-2.9589977-1.7127939-6.4834963-2.0199002-9.9916744-2.1938213-4.5994439-.1696981-9.6122217-.0810043-14.3488065-.1028834-5.9779894-.0004152-10.6558159.028832-15.2119156-1.0922974-5.139763-1.381211-7.7639016-3.3199843-6.2389689-5.8720813,1.3684202-2.5919641,9.6516076-4.2551846,15.6117555-4.0585391,7.8260022-.0390292,17.872305-.0224406,25.5107818-.0091924,12.5719948.0832934,17.2103741.4547469,17.242918,14.8402682.0941258,4.6799319.1198539,10.1769366-.0599511,14.8962228-.2350968,3.4934818-.3141061,7.0134346-2.3730151,9.8166906-2.0066289,2.607945-5.9184099,3.1824389-11.8925704,3.3165881-4.4674079.0875534-8.9315617.042341-13.5116877.0533603-8.679591-.4381412-24.6662757,1.7300728-30.3170787-3.7695042l-.0491471-.0550851ZM1036.1225851,44.1872746c-2.3105345,2.5401046-5.7317984,3.4650189-10.6585396,4.0940388-7.198124.5152278-16.9080414,1.2843542-23.436965-1.3531596-6.9197422-2.9394923-6.8933288-9.5531713-.258035-12.4998923,3.6966735-1.7800086,9.3519374-2.0098857,15.2012686-1.9238174,7.4703288.3335541,14.8248971.0499631,19.2924277,4.7826916,1.6084228,2.0202748,1.6243946,4.7790077-.0739535,6.8207012l-.0662032.0794376Z"/>
  </svg>
);

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
  help: <I d={<><circle cx="12" cy="12" r="9" /><path d="M9.2 9.3a2.9 2.9 0 1 1 3.6 3.4c-.6.2-.8.7-.8 1.3v.4" /><circle cx="12" cy="17.6" r=".7" fill="currentColor" /></>} size={17} />,
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

  /* wheel needs a non-passive listener to preventDefault. Registered once and
     reading live values from a ref, so it isn't torn down on every value change. */
  const live = useRef({ v, step, clamp, set });
  live.current = { v, step, clamp, set };
  useEffect(() => {
    const el = trk.current; if (!el) return;
    const h = (e) => {
      e.preventDefault();
      const { v: cv, step: cs, clamp: cc, set: css } = live.current;
      const dir = (e.deltaY || e.deltaX) > 0 ? -1 : 1;
      css(cc(cv + dir * cs * (e.shiftKey ? 10 : 1)));
    };
    el.addEventListener("wheel", h, { passive: false });
    return () => el.removeEventListener("wheel", h);
  }, []);

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

/* ---------------- tooltip copy ---------------- */
const TIPS = {
  "Columns": "How many vertical divisions the tile is cut into.",
  "Col rhythm": "How column widths are decided. Even is uniform, dyadic halves repeatedly, random is free.",
  "Rows": "How many horizontal divisions the tile is cut into.",
  "Row rhythm": "How row heights are decided. Same options as columns.",
  "Voids": "Chance that a cell is left empty, punching holes through to the layer below.",
  "Seed": "The random number behind this layer. Same seed always gives the same pattern.",
  "Min count": "Fewest gradient stripes a single cell can hold.",
  "Max count": "Most gradient stripes a single cell can hold. High values give fine mesh, low give heavy blocks.",
  "Widths": "How stripe widths vary inside a cell.",
  "Density ↔": "Shifts stripe density from left to right across the tile.",
  "Density ↕": "Shifts stripe density from top to bottom across the tile.",
  "Vert bias": "How often stripes run vertically instead of horizontally.",
  "Shape": "The gradient curve. Linear is a plain black-to-white ramp, triangle goes dark-light-dark, steps hard-edges it.",
  "Gamma": "Bends the ramp toward the dark or light end.",
  "Max steps": "How many hard bands a stepped ramp can be cut into.",
  "Inverts": "Chance a cell flips its gradient, so light becomes dark.",
  "Mode": "Repeat lays the tile in a regular grid. Collage cuts the canvas into cells of varying shape and stretches a tile into each.",
  "Across": "How many times the tile repeats horizontally.",
  "Down": "How many times the tile repeats vertically.",
  "Cell sizes": "Whether repeated tiles are all the same size or vary.",
  "Cells": "How many pieces the canvas is cut into.",
  "Evenness": "Low makes cell sizes wildly uneven. High keeps them close to equal.",
  "Ratio range": "How far cell proportions can stray from square.",
  "Split axis": "Auto cuts along the longer side, keeping cells squarish. Random gives extreme shapes.",
  "Gap": "Space between cells, showing the background through as a grid.",
  "Rotate %": "Chance each cell's tile is turned by a quarter turn.",
  "Flip %": "Chance each cell's tile is mirrored.",
  "X %": "Moves the layer sideways.",
  "Y %": "Moves the layer up and down.",
  "Width %": "Stretches the layer horizontally. Over 100 pushes it past the canvas edge.",
  "Height %": "Stretches the layer vertically.",
  "Rotate": "Turns the whole layer. Off-square angles need width and height above 100 to keep the canvas covered.",
  "Skew": "Slants the layer sideways.",
  "Name": "What this layer is called. Carries through to the exported SVG as the group name.",
  "Role": "Paint draws the layer. Mask uses its brightness to hide parts of the layer below.",
  "Blend": "How this layer mixes with the ones under it. Difference is the default and gives the smoothest results.",
  "Opacity": "How strongly this layer shows.",
};

/* ---------------- atoms ---------------- */
const Row = ({ label, children }) => (
  <div className="row">
    <div className={`lab${TIPS[label] ? " tipped" : ""}`}>
      {label}
      {TIPS[label] && <span className="tip">{TIPS[label]}</span>}
    </div>
    <div className="ctl">{children}</div>
  </div>
);
const Sel = ({ v, set, opts }) => (
  <select className="sel" value={v} onChange={(e) => set(e.target.value)}>
    {opts.map((o) => <option key={o} value={o}>{o}</option>)}
  </select>
);
const Toggle = ({ v, set, label }) => (
  <button className={`btn${v ? " on" : ""}`} onClick={() => set(!v)}>{label}</button>
);
const Act = ({ onClick, icon, label, on, hero, dis, glow }) => (
  <button className={`btn${on ? " on" : ""}${hero ? " hero" : ""}${dis ? " dis" : ""}${glow ? " glow" : ""}`}
    onClick={onClick} disabled={dis} title={label}>
    {icon}<span>{label}</span>
  </button>
);

/* Hover menus open at once and close on a delay, so moving diagonally toward
   an option — or clipping the edge of the button — cannot dismiss them. */
function useHoverMenu(delay = 160) {
  const [open, setOpen] = useState(false);
  const t = useRef(0);
  useEffect(() => () => clearTimeout(t.current), []);
  return {
    open, setOpen,
    bind: {
      onMouseEnter: () => { clearTimeout(t.current); setOpen(true); },
      onMouseLeave: () => { clearTimeout(t.current); t.current = setTimeout(() => setOpen(false), delay); },
    },
  };
}

/* Menus are positioned in viewport space rather than inside the toolbar, so a
   scrolling or tightly-packed bar can never clip them. */
function MenuButton({ menu, children }) {
  const ref = useRef(null);
  const m = useHoverMenu();
  const [pos, setPos] = useState(null);
  useEffect(() => {
    if (!m.open || !ref.current) { setPos(null); return; }
    const r = ref.current.getBoundingClientRect();
    setPos({ top: r.bottom + 4, right: Math.max(8, window.innerWidth - r.right) });
  }, [m.open]);
  return (
    <span className="menuwrap" ref={ref} {...m.bind}>
      {children(m)}
      {m.open && pos && (
        <span className="popmenu" style={{ top: pos.top, right: pos.right }}>{menu(m)}</span>
      )}
    </span>
  );
}

/* ---------------- artboard (canvas) ----------------
   The preview is rasterised, not a DOM tree. A tile with 400 rects placed in
   40 cells is 16,000 SVG nodes but only 400 fills: each unique tile is drawn
   once into an offscreen canvas and every instance is a single blit. Moving a
   placement slider costs nothing but blits. SVG is used for export only. */
const RASTER = new Map();
const RASTER_MAX = 40;

function rasterTile(tile, px) {
  const key = `${tile.key}@${px}`;
  const hit = RASTER.get(key);
  if (hit) return hit;

  const c = document.createElement("canvas");
  c.width = px; c.height = px;
  const g = c.getContext("2d");
  const k = px / U;
  for (const r of tile.rects) {
    const gd = GRADS.get(r.g);
    const [x1, y1, x2, y2] = DIRS[gd.dir];
    const grad = g.createLinearGradient(
      (r.x + x1 * r.w) * k, (r.y + y1 * r.h) * k,
      (r.x + x2 * r.w) * k, (r.y + y2 * r.h) * k);
    for (const [o, v] of gd.stops) grad.addColorStop(o, `rgb(${v},${v},${v})`);
    g.fillStyle = grad;
    g.fillRect(r.x * k, r.y * k, r.w * k, r.h * k);
  }
  RASTER.set(key, c);
  if (RASTER.size > RASTER_MAX) RASTER.delete(RASTER.keys().next().value);
  return c;
}

function paintLayer(ctx, b, rasters, scale) {
  for (const it of b.inst) {
    const img = rasters.get(it.tile);
    if (!img) continue;
    ctx.save();
    const m = mMul(mMul([scale, 0, 0, scale, 0, 0], b.m), it.m);
    ctx.setTransform(m[0], m[1], m[2], m[3], m[4], m[5]);
    ctx.drawImage(img, 0, 0, U, U);
    ctx.restore();
  }
}

/* luminance of the mask becomes the alpha of the layer beneath it */
function applyMask(layerCv, maskB, rasters, scale, invert) {
  const mc = document.createElement("canvas");
  mc.width = layerCv.width; mc.height = layerCv.height;
  const mg = mc.getContext("2d");
  mg.fillStyle = invert ? "#fff" : "#000";
  mg.fillRect(0, 0, mc.width, mc.height);
  paintLayer(mg, maskB, rasters, scale);
  mg.setTransform(1, 0, 0, 1, 0, 0);

  const d = mg.getImageData(0, 0, mc.width, mc.height);
  const px = d.data;
  for (let i = 0; i < px.length; i += 4) {
    const lum = (px[i] * 0.2126 + px[i + 1] * 0.7152 + px[i + 2] * 0.0722);
    px[i + 3] = invert ? 255 - lum : lum;
  }
  mg.putImageData(d, 0, 0);

  const lg = layerCv.getContext("2d");
  lg.setTransform(1, 0, 0, 1, 0, 0);
  lg.globalCompositeOperation = "destination-in";
  lg.drawImage(mc, 0, 0);
  lg.globalCompositeOperation = "source-over";
}

const Artboard = React.memo(function Artboard({ model, w, h }) {
  const ref = useRef(null);

  useEffect(() => {
    const cv = ref.current; if (!cv || !w || !h) return;
    const dpr = Math.min(2, window.devicePixelRatio || 1);
    const cw = Math.max(1, Math.round(w * dpr)), ch = Math.max(1, Math.round(h * dpr));
    if (cv.width !== cw || cv.height !== ch) { cv.width = cw; cv.height = ch; }
    const ctx = cv.getContext("2d");

    /* raster resolution scales with how large each instance actually lands */
    const maxInst = model.layers.reduce((a, b) => Math.max(a, b.inst.length), 1);
    const px = Math.max(192, Math.min(1024,
      1 << Math.ceil(Math.log2(Math.max(192, cw / Math.sqrt(maxInst))))));
    const rasters = new Map(model.tiles.map((t) => [t.key, rasterTile(t, px)]));

    const scale = cw / model.W;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, cw, ch);
    if (model.bg !== "none") { ctx.fillStyle = model.bg; ctx.fillRect(0, 0, cw, ch); }

    /* layers composite against each other, not the background — matches the
       isolation group used in the SVG export */
    const stage = document.createElement("canvas");
    stage.width = cw; stage.height = ch;
    const sg = stage.getContext("2d");

    model.layers.forEach((b, i) => {
      let src = stage, sctx = sg, direct = true;
      if (b.mask) { /* masked layers need their own surface first */
        src = document.createElement("canvas");
        src.width = cw; src.height = ch;
        sctx = src.getContext("2d");
        direct = false;
      }
      sctx.save();
      if (direct) {
        sg.globalCompositeOperation = i === 0 ? "source-over" : b.L.blend;
        sg.globalAlpha = b.L.opacity;
      }
      paintLayer(sctx, b, rasters, scale);
      sctx.restore();
      if (!direct) {
        applyMask(src, b.mask, rasters, scale, b.mask.L.maskInvert);
        sg.setTransform(1, 0, 0, 1, 0, 0);
        sg.globalCompositeOperation = i === 0 ? "source-over" : b.L.blend;
        sg.globalAlpha = b.L.opacity;
        sg.drawImage(src, 0, 0);
      }
      sg.setTransform(1, 0, 0, 1, 0, 0);
      sg.globalCompositeOperation = "source-over";
      sg.globalAlpha = 1;
    });

    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.drawImage(stage, 0, 0);
  }, [model, w, h]);

  return (
    <div className="art" style={{ width: w, height: h }}>
      <canvas ref={ref} style={{ width: "100%", height: "100%", display: "block" }} />
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
export default function VisualLoom() {
  const [W, setW] = useState(3840);
  const [H, setH] = useState(3840);
  const [bg, setBg] = useState("#ffffff");
  const [layers, setLayers] = useState([]);
  const [tiles, setTiles] = useState([]);
  const [looks, setLooks] = useState([]);
  const [lookName, setLookName] = useState("");
  const [importCode, setImportCode] = useState("");
  const [sel, setSel] = useState(null);
  const [tab, setTab] = useState("Grid");
  const [expand, setExpand] = useState(true);
  const [minLayers, setMinLayers] = useState(2);
  const [maxLayers, setMaxLayers] = useState(6);
  const [help, setHelp] = useState(false);
  const [savedHint, setSavedHint] = useState(false);
  const [msg, setMsg] = useState("");
  const [drawer, setDrawer] = useState(null);
  const [png, setPng] = useState(null);
  const [pngSize, setPngSize] = useState([0, 0]);
  const [svgMode, setSvgMode] = useState(true);
  const fileRef = useRef(null);
  const stageRef = useRef(null);

  const [fit, setFit] = useState({ w: 200, h: 200 });

  /* live drag state — declared before the document memos that read it */
  const [drift, setDrift] = useState(null);
  const [stepSeed, setStepSeed] = useState(false);
  const dragRef = useRef(null);
  const rafRef = useRef(0);
  /* Placement each layer was created with. Double-click returns here rather
     than to a flat default, so reset restores the generated composition
     instead of a different one. */
  const homeRef = useRef(new Map());
  const rememberHome = (ls) => {
    ls.forEach((l) => homeRef.current.set(l.id,
      { x: l.x, y: l.y, rot: l.rot, skew: l.skew, w: l.w, h: l.h, flipX: l.flipX, flipY: l.flipY }));
  };
  const peekRef = useRef(false);
  const [peek, setPeek] = useState(false);
  const glideRef = useRef(null);
  const glideRaf = useRef(0);
  const [autoDrift, setAutoDrift] = useState(false);

  const doc = useMemo(() => ({ W, H, bg, layers, tiles }), [W, H, bg, layers, tiles]);
  const liveDoc = useMemo(() => {
    if (peek) {
      /* hold to see the composition as it was generated — a view, never an edit */
      const home = homeRef.current;
      return { ...doc, layers: doc.layers.map((l) => ({ ...l, ...(home.get(l.id) || {}) })) };
    }
    return drift ? { ...doc, drift } : doc;
  }, [doc, drift, peek]);
  /* drift must not be deferred — it needs to track the pointer */
  const previewDoc = useDeferredValue(liveDoc);
  const shownDoc = (drift || peek) ? liveDoc : previewDoc;
  const model = useMemo(() => buildModel(shownDoc), [shownDoc]);
  const rectCount = useMemo(() => {
    let n = 0;
    const per = new Map(model.tiles.map((t) => [t.key, t.rects.length]));
    for (const b of model.layers) for (const it of b.inst) n += per.get(it.tile) || 0;
    return n;
  }, [model]);
  const L = layers.find((l) => l.id === sel) || layers[0];

  /* saved looks persist in localStorage */
  useEffect(() => {
    (async () => {
      try {
        const raw = localStorage.getItem("visual_loom_looks")
          || localStorage.getItem("pd_loomrift_looks")
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

  /* ---- canvas drift ----
     Drag anywhere on the artwork to slide the layers against each other.
     Held in a ref and pushed through rAF so pointer events never queue up
     behind a React render; released values are committed to the layers. */
  /* ---- drift transport ----
     Accumulated drift is kept apart from the live delta, so releasing Shift
     mid-drag rebases the origin instead of snapping. Distance is curved so a
     drag starts precise and accelerates the further it is pulled, and release
     velocity carries on as momentum. */
  const ACCEL = 2.1;                   /* how hard the curve bites */
  const curve = (v, boost) => {
    const a = Math.abs(v);
    return Math.sign(v) * (a + ACCEL * a * a) * boost;
  };

  const emit = (d) => {
    const b = d.alt ? 8 : 1;
    setDrift(d.shift
      ? { dx: d.acc.dx, dy: d.acc.dy, rx: d.acc.rx + curve(d.rx || 0, b) }
      : { dx: d.acc.dx + curve(d.rawx || 0, b), dy: d.acc.dy + curve(d.rawy || 0, b), rx: d.acc.rx });
  };

  const rebase = (d) => {
    const b = d.alt ? 8 : 1;
    if (d.shift) d.acc.rx += curve(d.rx || 0, b);
    else { d.acc.dx += curve(d.rawx || 0, b); d.acc.dy += curve(d.rawy || 0, b); }
    d.rawx = 0; d.rawy = 0; d.rx = 0;
    d.x = d.lastX; d.y = d.lastY;
  };

  const commit = (cur) => {
    if (!cur || (!cur.dx && !cur.dy && !cur.rx)) return;
    setLayers((ls) => {
      const vis = ls.filter((l) => l.visible);
      const idx = new Map(vis.map((l, i) => [l.id, i]));
      return ls.map((l) => idx.has(l.id) ? driftLayer(l, cur, idx.get(l.id), vis.length) : l);
    });
  };

  const onStageDown = (e) => {
    if (!layers.length || drawer || help) return;
    if (e.target.closest(".drawer, .help, .drifthint")) return;
    /* Grabbing mid-coast banks whatever the coast has travelled so far, then
       starts the new drag from there. Without this the coast's distance was
       discarded and the canvas snapped back to the pre-flick state. */
    if (glideRaf.current) { cancelAnimationFrame(glideRaf.current); glideRaf.current = 0; }
    const g = glideRef.current;
    glideRef.current = null;
    if (g) commit({ dx: g.dx, dy: g.dy, rx: g.rx });
    if (autoDrift) setAutoDrift(false);
    e.currentTarget.setPointerCapture(e.pointerId);
    dragRef.current = {
      x: e.clientX, y: e.clientY, lastX: e.clientX, lastY: e.clientY, t: performance.now(),
      rect: e.currentTarget.getBoundingClientRect(),
      acc: { dx: 0, dy: 0, rx: 0 }, rawx: 0, rawy: 0, rx: 0,
      vx: 0, vy: 0, vr: 0,
      shift: e.shiftKey, alt: e.altKey, seeds: layers.map((l) => l.seed), crossed: 0,
    };
    setDrift({ dx: 0, dy: 0, rx: 0 });
  };

  const onStageMove = (e) => {
    const d = dragRef.current; if (!d) return;
    const now = performance.now();
    const dt = Math.max(8, now - d.t);
    const pvx = (e.clientX - d.lastX) / d.rect.width / dt;
    const pvy = (e.clientY - d.lastY) / d.rect.height / dt;
    d.vx = d.vx * 0.7 + pvx * 0.3;                 /* smoothed release velocity */
    d.vy = d.vy * 0.7 + pvy * 0.3;
    d.t = now; d.lastX = e.clientX; d.lastY = e.clientY;

    if (e.shiftKey !== d.shift || e.altKey !== d.alt) {
      rebase(d); d.shift = e.shiftKey; d.alt = e.altKey;
    }
    const nx = (e.clientX - d.x) / Math.max(1, d.rect.width);
    const ny = (e.clientY - d.y) / Math.max(1, d.rect.height);
    if (d.shift) d.rx = nx; else { d.rawx = nx; d.rawy = ny; }

    if (rafRef.current) return;                    /* coalesce to one per frame */
    rafRef.current = requestAnimationFrame(() => {
      rafRef.current = 0;
      emit(d);
      if (stepSeed) {
        const steps = Math.floor(Math.abs(d.acc.dx + (d.rawx || 0)) * 6);
        if (steps !== d.crossed) {
          d.crossed = steps;
          const k = steps % Math.max(1, layers.length);
          setLayers((ls) => ls.map((l, i) => i === k
            ? { ...l, seed: (d.seeds[i] + steps * 977) % 100000 } : l));
        }
      }
    });
  };

  /* Shift and Alt can be pressed or released without moving the pointer */
  useEffect(() => {
    const onKey = (e) => {
      const d = dragRef.current;
      if (!d || (e.key !== "Shift" && e.key !== "Alt")) return;
      const down = e.type === "keydown";
      const which = e.key === "Shift" ? "shift" : "alt";
      if (down === d[which]) return;
      rebase(d); d[which] = down; emit(d);
    };
    window.addEventListener("keydown", onKey);
    window.addEventListener("keyup", onKey);
    return () => { window.removeEventListener("keydown", onKey); window.removeEventListener("keyup", onKey); };
  }, []);

  const onStageUp = (e) => {
    const d = dragRef.current; if (!d) return;
    rebase(d);
    const cur = { ...d.acc };
    const boost = d.alt ? 8 : 1;
    /* velocity at release, in units of screen-widths per ms */
    const fling = d.shift
      ? { dx: 0, dy: 0, rx: d.vx * 95 * boost }
      : { dx: d.vx * 95 * boost, dy: d.vy * 95 * boost, rx: 0 };
    dragRef.current = null;
    if (rafRef.current) { cancelAnimationFrame(rafRef.current); rafRef.current = 0; }
    try { e.currentTarget.releasePointerCapture(e.pointerId); } catch { }

    const speed = Math.hypot(fling.dx, fling.dy) + Math.abs(fling.rx);
    if (speed < 0.035) { setDrift(null); commit(cur); return; }

    /* coast on: keep the accumulated drift live and keep adding to it while
       the velocity decays, then bake the whole travel in one edit */
    glideRef.current = { ...cur, vdx: fling.dx, vdy: fling.dy, vrx: fling.rx };
    const tick = () => {
      const g = glideRef.current;
      if (!g) return;
      g.dx += g.vdx; g.dy += g.vdy; g.rx += g.vrx;
      g.vdx *= 0.895; g.vdy *= 0.895; g.vrx *= 0.895;   /* fabric, not ice */
      setDrift({ dx: g.dx, dy: g.dy, rx: g.rx });
      if (Math.hypot(g.vdx, g.vdy) + Math.abs(g.vrx) > 0.0018) {
        glideRaf.current = requestAnimationFrame(tick);
      } else {
        const final = { dx: g.dx, dy: g.dy, rx: g.rx };
        glideRef.current = null;
        setDrift(null);
        commit(final);
      }
    };
    glideRaf.current = requestAnimationFrame(tick);
  };

  /* ---- auto drift ----
     Wanders on its own from two slow sine waves of different periods, so it
     never settles into a short loop. Touching the canvas switches it off.
     Never committed to the layers — it is a view, not an edit. */
  useEffect(() => {
    if (!autoDrift || !layers.length) return;
    let raf = 0;
    const t0 = performance.now();
    const tick = () => {
      if (!dragRef.current && !glideRef.current) {
        const t = (performance.now() - t0) / 1000;
        setDrift({
          dx: Math.sin(t * 0.21) * 0.9 + Math.sin(t * 0.067) * 0.5,
          dy: Math.sin(t * 0.13 + 1.7) * 0.28,
          rx: Math.sin(t * 0.089 + 0.6) * 0.35,
        });
      }
      raf = requestAnimationFrame(tick);
    };
    raf = requestAnimationFrame(tick);
    return () => { cancelAnimationFrame(raf); setDrift(null); };
  }, [autoDrift, layers.length]);

  /* Wheel drives layers apart in scale, alternating direction by depth, so the
     stack breathes through itself. Matrix-only like the drag, so it stays at
     frame rate; committed straight to the layers and covered by undo. */
  useEffect(() => {
    const el = stageRef.current; if (!el) return;
    const cl = (v) => Math.max(4, Math.min(1200, v));
    const h = (e) => {
      if (!layers.length || drawer || help) return;
      e.preventDefault();
      const step = (e.shiftKey ? 0.075 : 0.028) * (e.deltaY > 0 ? -1 : 1);
      setLayers((ls) => {
        const vis = ls.filter((l) => l.visible);
        const idx = new Map(vis.map((l, i) => [l.id, i]));
        return ls.map((l) => {
          if (!idx.has(l.id)) return l;
          const k = 1 + step * (idx.get(l.id) % 2 === 0 ? 1 : -1);
          return { ...l, w: cl(l.w * k), h: cl(l.h * k) };
        });
      });
    };
    el.addEventListener("wheel", h, { passive: false });
    return () => el.removeEventListener("wheel", h);
  }, [layers.length, drawer, help]);

  /* ---- keyboard ----
     Arrows nudge, Space rolls a new look, Tab held peeks at the generated
     composition. All ignored while a text field has focus. */
  useEffect(() => {
    const typing = () => {
      const t = document.activeElement?.tagName;
      return t === "INPUT" || t === "TEXTAREA" || t === "SELECT";
    };
    const onDown = (e) => {
      if (typing() || drawer || help) return;

      if (e.code === "Space") {
        e.preventDefault();
        randomLook();
        return;
      }
      if (e.key === "Tab" && layers.length) {
        e.preventDefault();
        if (peekRef.current) return;
        peekRef.current = true;
        setPeek(true);
        return;
      }
      const step = e.shiftKey ? 0.06 : 0.012;     /* fine by default, coarse with shift */
      const map = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1] };
      const v = map[e.key];
      if (!v || !layers.length) return;
      e.preventDefault();
      const d = e.altKey
        ? { dx: 0, dy: 0, rx: v[0] * step }       /* alt+arrow twists */
        : { dx: v[0] * step, dy: v[1] * step, rx: 0 };
      commit(d);
    };
    const onUp = (e) => {
      if (e.key === "Tab" && peekRef.current) { peekRef.current = false; setPeek(false); }
    };
    window.addEventListener("keydown", onDown);
    window.addEventListener("keyup", onUp);
    return () => { window.removeEventListener("keydown", onDown); window.removeEventListener("keyup", onUp); };
  });

  const resetDrift = () => {
    if (!layers.length) return;
    setLayers((ls) => ls.map((l) => {
      const home = homeRef.current.get(l.id);
      return home ? { ...l, ...home } : { ...l, x: 0, y: 0, rot: 0, skew: 0, w: 100, h: 100 };
    }));
    flash("Back to generated view");
  };
  const flash = (t) => { setMsg(t); setTimeout(() => setMsg(""), 1800); };

  /* ---- random look ----
     Composes from a few known-good arrangements rather than randomising freely.
     Blend mode is never assigned here — every layer keeps the difference
     default until it is changed by hand in the Layer tab. */
  const randomLook = () => {
    const r = mulberry32(Math.floor(Math.random() * 1e9));

    /* depth first — the range is a hard constraint, style adapts to it */
    const lo = Math.min(minLayers, maxLayers), hi = Math.max(minLayers, maxLayers);
    const n = rint(r, lo, hi);
    const strategy = strategyFor(n, r);
    const plan = grainPlan(strategy, n, r);

    const ls = plan.map((g, i) => {
      const base = i === 0;
      /* chunky layers lean to repeat, fine ones take collage more often */
      const collageOdds = g === "chunky" ? 0.28 : g === "fine" ? 0.5 : 0.4;
      return newLayer({
        name: base ? "Base" : `Layer ${i + 1}`,
        ...randTile(r, g),
        ...(r() < collageOdds ? randCollage(r, g) : randRepeat(r, g)),
        opacity: base ? 1 : (r() < (n <= 4 ? 0.6 : 0.3) ? 1 : +rflt(r, 0.45, 0.9).toFixed(2)),
        ...randPlace(r, base),
      });
    });

    trimToBudget(ls);
    rememberHome(ls);
    setLayers(ls); setSel(ls[0].id);
    if (!savedHint) { setSavedHint(true); flash("Keep one you like — save it in Looks"); }
    else flash(`${strategy} · ${n} layers`);
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
    try { localStorage.setItem("visual_loom_looks", JSON.stringify(list)); } catch { }
  };
  const saveLook = () => {
    settle();
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
      rememberHome(d.layers);
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
    if (!L) return;
    const t = { id: ++TID, name: L.name, params: genParams(L), on: true };
    setTiles((ts) => [...ts, t]);
    flash(`Baked "${t.name}" to tiles`);
  };
  const delTile = (id) => setTiles((ts) => ts.filter((t) => t.id !== id));
  const toggleTile = (id) => setTiles((ts) => ts.map((t) => (t.id === id ? { ...t, on: !t.on } : t)));

  /* ---- export ---- */
  /* Exports and saves read committed state, so any motion is settled first —
     the coast is banked, auto-drift switched off, and the live offset cleared. */
  const settle = () => {
    if (autoDrift) setAutoDrift(false);
    if (glideRaf.current) { cancelAnimationFrame(glideRaf.current); glideRaf.current = 0; }
    const g = glideRef.current;
    glideRef.current = null;
    if (g) commit({ dx: g.dx, dy: g.dy, rx: g.rx });
    if (dragRef.current) { rebase(dragRef.current); commit({ ...dragRef.current.acc }); dragRef.current = null; }
    setDrift(null);
  };

  const openSVG = (sep = expand) => {
    settle();
    setSvgMode(sep);
    tryDownload(svgDataUrl(buildSVG(doc, sep)), `VisualLoom_${Date.now()}.svg`);
    setDrawer("svg");
  };
  const openPNG = (frac = 1) => {
    settle();
    const w = Math.round(W * frac), h = Math.round(H * frac);
    setDrawer("png"); setPng(null); setPngSize([w, h]);
    const img = new Image();
    img.onload = () => {
      try {
        const c = document.createElement("canvas");
        c.width = w; c.height = h;
        c.getContext("2d").drawImage(img, 0, 0, w, h);
        const url = c.toDataURL("image/png");
        setPng(url); tryDownload(url, `VisualLoom_${w}x${h}.png`);
      } catch { setPng("error"); }
    };
    img.onerror = () => setPng("error");
    img.src = svgDataUrl(buildSVG(doc, true));
  };
  const presetJSON = () => JSON.stringify({ v: 8, W, H, bg, layers, tiles }, null, 1);
  const openPreset = () => {
    settle();
    tryDownload("data:application/json;charset=utf-8," + encodeURIComponent(presetJSON()), "VisualLoom_preset.json");
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
        rememberHome(ls);
        setLayers(ls); setSel(ls[0]?.id); flash("Preset loaded");
      } catch { flash("Couldn't read that file"); }
    };
    rd.readAsText(f); e.target.value = "";
  };

  /* Strip back to a single default layer — one square, one black-to-white
     ramp — so the building block is visible again. */
  const resetDoc = () => {
    const n = newLayer({
      name: "Base", cols: 1, rows: 1, freqMin: 1, freqMax: 1,
      colMode: "even", rowMode: "even", stripeMode: "even",
      axisBias: 1, invertChance: 0, voidChance: 0, rampMode: "linear",
      gamma: 1, pingPong: false, mode: "repeat", tileX: 1, tileY: 1,
      tileRot: false, tileFlip: false,
    });
    homeRef.current.clear();
    rememberHome([n]);
    setTiles([]); setLayers([n]); setSel(n.id); setTab("Grid");
    setAutoDrift(false); setDrift(null);
    flash("Reset to one gradient");
  };

  const addLayer = () => { const n = newLayer(); rememberHome([n]); setLayers((ls) => [...ls, n]); setSel(n.id); setTab("Layer"); };
  const dupLayer = () => { if (!L) return; const n = { ...L, id: ++UID, name: L.name + " copy" }; rememberHome([n]); setLayers((ls) => [...ls, n]); setSel(n.id); };
  const delLayer = () => {
    if (!L || layers.length < 2) return;
    const i = layers.findIndex((l) => l.id === sel);
    const ls = layers.filter((l) => l.id !== sel);
    setLayers(ls); setSel(ls[Math.max(0, i - 1)].id);
  };
  const move = (d) => {
    if (!L) return;
    const i = layers.findIndex((l) => l.id === sel), j = i + d;
    if (j < 0 || j >= layers.length) return;
    const ls = [...layers]; [ls[i], ls[j]] = [ls[j], ls[i]]; setLayers(ls);
  };

  const drawerText = drawer === "svg" ? buildSVG(doc, svgMode) : drawer === "preset" ? presetJSON() : "";
  const activeTiles = tiles.filter((t) => t.on).length;

  const canvasControls = (
    <>
      <div className="sizechips">
        {SIZES.map(([n, w, h]) => (
          <button key={n} className={`chip${W === w && H === h ? " on" : ""}`} onClick={() => { setW(w); setH(h); }}>{n}</button>
        ))}
      </div>
      <div className="dims">
        <input className="num-in" type="number" value={W} min={200} max={8000}
          onChange={(e) => setW(Math.max(200, +e.target.value || 200))} />
        <span className="x">×</span>
        <input className="num-in" type="number" value={H} min={200} max={8000}
          onChange={(e) => setH(Math.max(200, +e.target.value || 200))} />
      </div>
      <span className="vr" />
      <div className="grounds">
        <span className="cap glabel">Background</span>
        {GROUNDS.map(([g, gl]) => (
          <button key={g} className={`sw${bg === g ? " on" : ""}`} onClick={() => setBg(g)} title={`Background: ${gl}`}>
            <i style={g === "none"
              ? { backgroundImage: "linear-gradient(45deg,#555 25%,transparent 25%,transparent 75%,#555 75%),linear-gradient(45deg,#555 25%,#1a1a1a 25%,#1a1a1a 75%,#555 75%)", backgroundSize: "8px 8px", backgroundPosition: "0 0,4px 4px" }
              : { background: g }} />
            <span>{gl}</span>
          </button>
        ))}
      </div>
    </>
  );

  return (
    <div className="pd">
      <style>{CSS}</style>

      {/* ---- document bar ---- */}
      <div className="top">
        {canvasControls}
        <span style={{ flex: 1 }} />
        <Act onClick={undo} icon={Ico.undo} label="Undo" dis={!canUndo} />
        <Act onClick={redo} icon={Ico.redo} label="Redo" dis={!canRedo} />
        <span className="vr" />
        <span className="coachwrap">
          <Act onClick={randomLook} icon={Ico.spark} label="Random look" hero glow={!savedHint} />
          {!savedHint && (
            <span className="coach"><i className="arrow" />Start here</span>
          )}
        </span>
        <div className="rangefield" title="Layer count range for Random look">
          <span className="cap">Layers</span>
          <input className="mini" type="number" min={1} max={12} value={minLayers}
            onChange={(e) => {
              const v = Math.max(1, Math.min(12, +e.target.value || 1));
              setMinLayers(v); if (v > maxLayers) setMaxLayers(v);
            }} />
          <span className="dash">–</span>
          <input className="mini" type="number" min={1} max={12} value={maxLayers}
            onChange={(e) => {
              const v = Math.max(1, Math.min(12, +e.target.value || 1));
              setMaxLayers(v); if (v < minLayers) setMinLayers(v);
            }} />
        </div>
        <Act onClick={() => setLayers((ls) => ls.map((l) => ({ ...l, seed: Math.floor(Math.random() * 1e5) })))} icon={Ico.dice} label="Reseed all" />
        <span className="vr" />
        <MenuButton menu={(m) => (<>
          <span className="menuhead">Repeats</span>
          <button className={expand ? "on" : ""}
            onClick={() => { m.setOpen(false); setExpand(true); openSVG(true); }}>
            <span>Separate</span><em>easier to edit</em>
          </button>
          <button className={!expand ? "on" : ""}
            onClick={() => { m.setOpen(false); setExpand(false); openSVG(false); }}>
            <span>Linked</span><em>smaller file</em>
          </button>
        </>)}>
          {(m) => <Act onClick={() => { m.setOpen(false); openSVG(expand); }} icon={Ico.code} label="SVG" />}
        </MenuButton>
        <MenuButton menu={(m) => (<>
          <span className="menuhead">Size</span>
          {[[1, "Full"], [0.5, "Half"], [0.25, "Quarter"], [0.125, "Eighth"]].map(([f, n]) => (
            <button key={n} onClick={() => { m.setOpen(false); openPNG(f); }}>
              <span>{n}</span><em>{Math.round(W * f)}×{Math.round(H * f)}</em>
            </button>
          ))}
        </>)}>
          {(m) => <Act onClick={() => { m.setOpen(false); openPNG(1); }} icon={Ico.image} label="PNG" />}
        </MenuButton>
        <Act onClick={openPreset} icon={Ico.save} label="Save preset" />
        <Act onClick={() => fileRef.current?.click()} icon={Ico.open} label="Load preset" />
        <Act onClick={resetDoc} icon={Ico.reset} label="Reset" />

        <input ref={fileRef} type="file" accept=".json" onChange={loadJSON} style={{ display: "none" }} />
        <button className="iconbtn helpbtn" onClick={() => setHelp(true)} title="What is this?">{Ico.help}</button>
      </div>

      <div className="main">
        <div className="rail">
          {TABS.map(([t, icon]) => (
            <button key={t} className={`railbtn${tab === t ? " on" : ""}`} onClick={() => setTab(t)} title={t}>
              {icon}<span>{t}</span>
            </button>
          ))}
          <div className="railfoot">
            <div className="railmark">
              <Mark h={13} />
              <span className="brand">Visual Loom</span>
              <span className="ver">1.6</span>
            </div>
          </div>
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
              </div>
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

        <div className="stage" ref={stageRef}
          onPointerDown={onStageDown} onPointerMove={onStageMove}
          onPointerUp={onStageUp} onPointerCancel={onStageUp}
          onDoubleClick={resetDrift}
          style={{ cursor: layers.length && !drawer && !help ? (drift ? "grabbing" : "grab") : "default" }}>
          {layers.length === 0
            ? (
              <div className="empty-stage">
                <p className="lead">
                  Everything here is built from one ingredient: a square filled with a
                  black-to-white gradient. It gets sliced into stripes, stacked into tiles,
                  then stretched, rotated and layered until it stops looking like where it
                  came from.
                </p>
                <p className="cta">Hit <kbd>Space</kbd> to begin</p>
                <p className="alt">or press Random Look above</p>
              </div>
            )
            : <Artboard model={model} w={fit.w} h={fit.h} />}
          <div className={`toast${msg ? " on" : ""}`}>{msg}</div>
          {layers.length > 0 && (
            <div className="drifthint">
              <span>Drag · Shift twists · Alt far · Flick coasts · Wheel breathes · Arrows nudge · Tab peeks</span>
              <button className={`stepbtn${autoDrift ? " on" : ""}`}
                onClick={(e) => { e.stopPropagation(); setAutoDrift(!autoDrift); }}
                onPointerDown={(e) => e.stopPropagation()}
                title="Drift on its own until you touch the canvas">Auto</button>
              <button className={`stepbtn${stepSeed ? " on" : ""}`}
                onClick={(e) => { e.stopPropagation(); setStepSeed(!stepSeed); }}
                onPointerDown={(e) => e.stopPropagation()}
                title="Re-seed a layer as you sweep across">Step seeds</button>
            </div>
          )}

          {layers.length > 0 && (
            <div className="readout">
              {W}×{H} · {layers.filter((l) => l.visible).length}/{layers.length} layers · {tiles.length} tiles · {rectCount.toLocaleString()} shapes
            </div>
          )}

          {help && (
            <div className="help">
              <div className="helphead">
                <span className="title">About</span>
                <button className="iconbtn" onClick={() => setHelp(false)} title="Close">{Ico.close}</button>
              </div>
              <div className="helpbody">
                <div className="wrap">
                  <h4>What this is</h4>
                  <p>
                    A pattern generator built from one ingredient: a square filled with a
                    black-to-white gradient. That square gets sliced into stripes, stacked into
                    tiles, and those tiles get stretched, rotated and layered until the result
                    stops looking like where it came from.
                  </p>
                  <p>
                    Everything stays vector, so anything you make can be exported as an SVG at
                    any size without losing quality.
                  </p>

                  <h4>Start here</h4>
                  <p>
                    Press <b>Random Look</b> and keep pressing. Each press builds a whole new
                    design. The <b>Layers</b> range next to it sets how many layers get stacked —
                    low numbers give simple heavy blocks, high numbers give dense fine detail.
                  </p>
                  <p>
                    When something lands, open <b>Looks</b> and save it. Saved designs come back
                    exactly as they were, and can be copied out as a short code to share.
                  </p>

                  <h4>Drag the canvas</h4>
                  <p>
                    Drag anywhere on the artwork to slide the layers against each other. Each
                    layer moves at a different rate, so the pattern shifts continuously rather
                    than just panning. Drag sideways to slide and up or down to scale. Hold
                    <b> Shift</b> at any point during a drag to switch to twisting them apart,
                    and let go of it to carry on sliding.
                  </p>
                  <p>
                    The <b>wheel</b> pushes alternate layers apart in scale — one set growing while
                    the next shrinks — so the stack breathes through itself. Hold Shift for
                    coarser steps.
                  </p>
                  <p>
                    Drags accelerate the further you pull, so short movements stay precise and
                    long ones cover ground. Hold <b>Alt</b> to travel much faster still, and
                    flick and release to keep coasting for a second or two.
                  </p>
                  <p>
                    <b>Arrow keys</b> nudge by one small step, Shift-arrow by a larger one, and
                    Alt-arrow twists. Hold <b>Tab</b> at any time to peek at the composition as it
                    was generated, and let go to return to where you have drifted to.
                    <b> Space</b> rolls a new look.
                  </p>
                  <p>
                    Let go and it sticks. Double-click returns every layer to the position it was generated at. In the corner,
                    <b> Auto</b> drifts on its own until you touch the canvas, and
                    <b> Step seeds</b> adds a fresh pattern jump as you sweep.
                  </p>

                  <h4>Then take it apart</h4>
                  <p>
                    The icons down the left edit whichever layer is selected at the bottom.
                    Hover any control's name for a one-line explanation.
                  </p>
                  <dl>
                    <dt>Grid</dt><dd>How the tile is divided into cells, and the seed behind it.</dd>
                    <dt>Stripe</dt><dd>How many gradient bands fill each cell. The main coarse-to-fine control.</dd>
                    <dt>Ramp</dt><dd>The shape of the gradient itself — smooth, stepped, or peaked.</dd>
                    <dt>Layout</dt><dd>Tile the canvas in a regular grid, or cut it into cells of varying shape.</dd>
                    <dt>Place</dt><dd>Move, scale, rotate and skew the whole layer.</dd>
                    <dt>Layer</dt><dd>Blend mode, opacity, and whether the layer paints or masks.</dd>
                    <dt>Tiles</dt><dd>Save a layer's pattern for reuse, then mix several in a collage.</dd>
                    <dt>Looks</dt><dd>Save, restore and share whole designs.</dd>
                  </dl>

                  <h4>Layers</h4>
                  <p>
                    Add layers with the <b>+</b> at the bottom left. Every layer defaults to the
                    <b> difference</b> blend mode, which is what makes stacked gradients interact
                    instead of just covering each other. Two layers of the same pattern, one
                    slightly rotated, is usually more interesting than either alone.
                  </p>

                  <h4>Getting it out</h4>
                  <p>
                    <b>SVG</b> is the real output — full vector, one named group per layer.
                    <b> PNG</b> gives a flat image; hover the button for half, quarter and eighth
                    sizes. <b>Save</b> writes a preset file holding the whole document.
                    <b> Reset</b> strips everything back to a single black-to-white gradient, which
                    is the block the whole tool is built from.
                  </p>
                  <p>
                    Hovering <b>SVG</b> offers a choice for how repeated shapes are stored.
                    <b> Separate</b> writes each repeat as its own shape, so every one can be
                    edited on its own. <b>Linked</b> points them all at a single original, which
                    makes a much smaller file.
                  </p>

                  <h4>Aspect ratio</h4>
                  <p>
                    The presets at the top crop rather than stretch. A design is always built in a
                    square and the canvas shows a window onto it, so switching between 1:1 and
                    16:9 never distorts what you made.
                  </p>
                </div>
              </div>
            </div>
          )}

          {drawer && (
            <div className="drawer">
              <div className="drawerhead">
                <span className="title">{drawer === "png" ? `PNG export · ${pngSize[0]}×${pngSize[1]}` : drawer === "svg" ? `SVG export · ${svgMode ? "separate" : "linked"} repeats` : "Preset"}</span>
                {drawer !== "png" && (
                  <Act onClick={async () => flash((await copyText(drawerText)) ? "Copied" : "Clipboard blocked — select and copy")} icon={Ico.copy} label="Copy" />
                )}
                <button className="iconbtn" onClick={() => setDrawer(null)} title="Close">{Ico.close}</button>
              </div>
              <div className="drawerbody">
                <p className="note" style={{ margin: 0 }}>
                  {drawer === "png"
                    ? "A download was attempted. If nothing saved, right-click the image and choose Save image as."
                    : drawer === "preset"
                      ? "A download was attempted. If nothing saved, copy the text below."
                      : svgMode
                        ? "Every repeat is written as its own shape, so each can be edited separately. Hover the SVG button to switch to linked repeats for a much smaller file."
                        : "Repeats are linked to a single original, keeping the file small. Hover the SVG button to switch to separate repeats if you need to edit each one."}
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
