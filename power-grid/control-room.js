// Control room: SCADA single line, switching engine and 3D digital twin of the network.
// The switching engine mirrors engine/scada.py. When the view opens it recomputes every
// Python reference state and reports whether the browser results match.

const SQRT3 = Math.sqrt(3);
const esc = value => String(value).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmtInt = n => Math.round(n).toLocaleString('en-US');
const clockText = m => `${String(Math.floor(m / 60)).padStart(2, '0')}:${String(m % 60).padStart(2, '0')}`;
const reducedMotion = () => window.matchMedia('(prefers-reduced-motion: reduce)').matches;
const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));

// Switching engine (mirror of engine/scada.py)

function createEngine(net) {
  const byId = Object.fromEntries(net.branches.map(b => [b.id, b]));
  function topology(states) {
    const adjacency = {};
    for (const b of net.branches) {
      if (b.kind === 'switch' && !states[b.id]) continue;
      (adjacency[b.a] ||= []).push([b.id, b.b]);
      (adjacency[b.b] ||= []).push([b.id, b.a]);
    }
    const parent = {[net.source]: null}, order = [net.source];
    for (let i = 0; i < order.length; i++) {
      const node = order[i];
      for (const [id, next] of adjacency[node] || []) {
        if (parent[node] && parent[node].branch === id) continue;
        if (next in parent) return {loop: id};
        parent[next] = {node, branch: id};
        order.push(next);
      }
    }
    return {parent, order};
  }
  function analyze(states, fault) {
    const t = topology(states);
    if (t.loop) return {loop: t.loop};
    const {parent, order} = t, load = {};
    order.forEach(n => { load[n] = 0; });
    net.loads.forEach(l => { if (l.node in load) load[l.node] += l.mw; });
    for (let i = order.length - 1; i > 0; i--) load[parent[order[i]].node] += load[order[i]];
    const flows = {};
    order.slice(1).forEach(n => {
      const p = parent[n];
      flows[p.branch] = {from: p.node, to: n, mw: load[n], amps: load[n] * 1000 / (SQRT3 * net.nodes[n].kv * net.pf)};
    });
    const energized = new Set(order);
    const off = net.loads.filter(l => !energized.has(l.node));
    return {energized, parent, flows, load,
      customersOff: off.reduce((s, l) => s + l.customers, 0),
      mwServed: net.loads.filter(l => energized.has(l.node)).reduce((s, l) => s + l.mw, 0),
      faultLive: Boolean(fault) && energized.has(fault)};
  }
  function protect(states, fault) {
    const r = analyze(states, fault);
    if (r.loop || !r.faultLive) return {states, events: []};
    let node = fault;
    while (r.parent[node]) {
      const p = r.parent[node];
      if (byId[p.branch].device === 'breaker') return {states: {...states, [p.branch]: false}, events: [{type: 'trip', device: p.branch}]};
      node = p.node;
    }
    return {states, events: []};
  }
  function operate(states, device, close, fault) {
    const proposed = {...states, [device]: close};
    if (analyze(proposed, fault).loop) return {blocked: true};
    const guarded = protect(proposed, fault);
    const result = analyze(guarded.states, fault);
    const events = [...guarded.events];
    for (const [id, f] of Object.entries(result.flows)) {
      const limit = byId[id].limitA;
      if (limit && f.amps > limit) events.push({type: 'overload', device: id, amps: f.amps, limitA: limit});
    }
    return {states: guarded.states, events, result};
  }
  function verify(references) {
    let match = 0;
    for (const ref of references) {
      const r = analyze(ref.states, ref.fault);
      if (r.loop) continue;
      const nodes = [...r.energized].sort().join() === ref.energized.join();
      const ids = Object.keys(ref.amps);
      const amps = ids.length === Object.keys(r.flows).length && ids.every(id => r.flows[id] && Math.abs(r.flows[id].amps - ref.amps[id]) < 0.051);
      if (nodes && amps && r.customersOff === ref.customersOff) match++;
    }
    return {match, total: references.length};
  }
  const normal = () => Object.fromEntries(net.branches.filter(b => b.kind === 'switch').map(b => [b.id, b.normal]));
  return {byId, analyze, protect, operate, verify, normal};
}

// 3D math and mesh building

const V = {
  add: (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]],
  sub: (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]],
  mul: (a, s) => [a[0] * s, a[1] * s, a[2] * s],
  dot: (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2],
  cross: (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]],
  len: a => Math.hypot(a[0], a[1], a[2]),
  norm: a => { const l = Math.hypot(a[0], a[1], a[2]) || 1; return [a[0] / l, a[1] / l, a[2] / l]; },
  lerp: (a, b, t) => [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t]
};
function perspective(fovy, aspect, near, far) {
  const f = 1 / Math.tan(fovy / 2), nf = 1 / (near - far);
  return new Float32Array([f / aspect, 0, 0, 0, 0, f, 0, 0, 0, 0, (far + near) * nf, -1, 0, 0, 2 * far * near * nf, 0]);
}
function lookAt(eye, target, up) {
  const z = V.norm(V.sub(eye, target)), x = V.norm(V.cross(up, z)), y = V.cross(z, x);
  return new Float32Array([x[0], y[0], z[0], 0, x[1], y[1], z[1], 0, x[2], y[2], z[2], 0, -V.dot(x, eye), -V.dot(y, eye), -V.dot(z, eye), 1]);
}
function multiply(a, b) {
  const o = new Float32Array(16);
  for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) {
    let s = 0;
    for (let k = 0; k < 4; k++) s += a[k * 4 + r] * b[c * 4 + k];
    o[c * 4 + r] = s;
  }
  return o;
}
const sag = (a, b, depth, n = 10) => Array.from({length: n + 1}, (_, i) => {
  const t = i / n, p = V.lerp(a, b, t);
  p[1] -= depth * 4 * t * (1 - t);
  return p;
});

class Mesh {
  constructor() { this.v = []; }
  tri(a, b, c, n) { this.v.push(a[0], a[1], a[2], n[0], n[1], n[2], b[0], b[1], b[2], n[0], n[1], n[2], c[0], c[1], c[2], n[0], n[1], n[2]); }
  // Convex polygon. The normal is oriented away from `center` when one is given.
  poly(pts, center) {
    let n = V.norm(V.cross(V.sub(pts[1], pts[0]), V.sub(pts[2], pts[0])));
    if (center) {
      const fc = V.mul(pts.reduce((s, p) => V.add(s, p), [0, 0, 0]), 1 / pts.length);
      if (V.dot(n, V.sub(fc, center)) < 0) n = V.mul(n, -1);
    }
    for (let i = 1; i < pts.length - 1; i++) this.tri(pts[0], pts[i], pts[i + 1], n);
    return this;
  }
  box(x0, y0, z0, x1, y1, z1) {
    const c = [(x0 + x1) / 2, (y0 + y1) / 2, (z0 + z1) / 2];
    const p = i => [i & 1 ? x1 : x0, i & 2 ? y1 : y0, i & 4 ? z1 : z0];
    for (const f of [[0, 2, 6, 4], [1, 3, 7, 5], [0, 1, 5, 4], [2, 3, 7, 6], [0, 1, 3, 2], [4, 5, 7, 6]]) this.poly(f.map(p), c);
    return this;
  }
  prism(a, b, r, sides = 6, r2 = r, caps = true) {
    const d = V.norm(V.sub(b, a)), ref = Math.abs(d[1]) < 0.95 ? [0, 1, 0] : [1, 0, 0];
    const u = V.norm(V.cross(d, ref)), w = V.cross(d, u), ra = [], rb = [];
    for (let i = 0; i < sides; i++) {
      const t = (i / sides) * Math.PI * 2 + Math.PI / sides;
      const off = V.add(V.mul(u, Math.cos(t)), V.mul(w, Math.sin(t)));
      ra.push(V.add(a, V.mul(off, r)));
      rb.push(V.add(b, V.mul(off, r2)));
    }
    const c = V.mul(V.add(a, b), 0.5);
    for (let i = 0; i < sides; i++) { const j = (i + 1) % sides; this.poly([ra[i], ra[j], rb[j], rb[i]], c); }
    if (caps) { this.poly(ra, c); this.poly(rb, c); }
    return this;
  }
  tube(points, r, sides = 5) {
    for (let i = 0; i < points.length - 1; i++) this.prism(points[i], points[i + 1], r, sides, r, false);
    return this;
  }
  gable(x0, z0, x1, z1, y0, y1) {
    const zm = (z0 + z1) / 2, c = [(x0 + x1) / 2, (y0 + y1) / 2, zm];
    this.poly([[x0, y0, z0], [x1, y0, z0], [x1, y1, zm], [x0, y1, zm]], c);
    this.poly([[x0, y0, z1], [x1, y0, z1], [x1, y1, zm], [x0, y1, zm]], c);
    this.poly([[x0, y0, z0], [x0, y0, z1], [x0, y1, zm]], c);
    this.poly([[x1, y0, z0], [x1, y0, z1], [x1, y1, zm]], c);
    return this;
  }
  gem(c, r) {
    const p = [[c[0] + r, c[1], c[2]], [c[0] - r, c[1], c[2]], [c[0], c[1] + r * 1.4, c[2]], [c[0], c[1] - r * 1.4, c[2]], [c[0], c[1], c[2] + r], [c[0], c[1], c[2] - r]];
    for (const f of [[0, 2, 4], [4, 2, 1], [1, 2, 5], [5, 2, 0], [0, 4, 3], [4, 1, 3], [1, 5, 3], [5, 0, 3]]) this.poly(f.map(i => p[i]), c);
    return this;
  }
}

const hex = h => [parseInt(h.slice(1, 3), 16) / 255, parseInt(h.slice(3, 5), 16) / 255, parseInt(h.slice(5, 7), 16) / 255];
const C = {
  bg: hex('#0c1520'), bottom: hex('#070d14'), side: hex('#13253a'), rim: hex('#35506b'),
  ground: hex('#1a2d40'), yard: hex('#223244'), walk: hex('#2a3a4a'), road: hex('#111a24'), marking: hex('#6f8193'), kerb: hex('#3a4a5a'),
  steel: hex('#95a4b2'), concrete: hex('#b3bcc5'), porcelain: hex('#d6dee4'), tank: hex('#687886'), tankDark: hex('#4b5865'), fin: hex('#56646f'),
  wall: hex('#3a4a5b'), wall2: hex('#43546a'), house0: hex('#465566'), house1: hex('#516071'), house2: hex('#3d4b5b'), roof: hex('#29343f'), roof2: hex('#342f38'),
  floor: hex('#223040'), panel: hex('#a3b0bb'), desk: hex('#34414e'), screen: hex('#7cc4ff'), wallscreen: hex('#17385a'), chair: hex('#27313b'),
  win: hex('#ffd08a'), winOff: hex('#1e2833'), lamp: hex('#ffe3ad'), sign: hex('#f4b76b'), door: hex('#2a2521'),
  red: hex('#ff6b6b'), green: hex('#4ad89a'), hv: hex('#7eaaff'), mv: hex('#f4b76b'), lv: hex('#68e3c2'), dead: hex('#56636f'), fault: hex('#ff5a5a'),
  soil: hex('#3d3228'), sand: hex('#51452f'), barrier: hex('#f48787'), rmu: hex('#5f7a84'), css: hex('#687785'), awning: hex('#a3703d'),
  trunk: hex('#3f362b'), leaf: hex('#24473a'), joint: hex('#40505e'), fence: hex('#7a8a99'), marker: hex('#c9b27a'), white: hex('#e8eef2')
};

// Dynamic appearance helpers. S is the render snapshot of the switching state.
const wire = (node, kv) => S => S.on(node) ? {c: kv > 100 ? C.hv : kv > 1 ? C.mv : C.lv, e: 0.75} : {c: C.dead, e: 0};
const lights = node => S => S.on(node) ? {c: C.win, e: 1} : {c: C.winOff, e: 0};
const lampOf = id => S => S.closed(id) ? {c: C.red, e: 1} : {c: C.green, e: 1};

const PANELS = ['IC1', 'F1', 'F3', 'F5', 'BC', 'F2', 'F4', 'F6', 'IC2'];
const panelZ = id => -12.9 + PANELS.indexOf(id) * 1.35 + 0.625;
const PIT = {x0: 0.5, x1: 3.5, z0: 8.6, z1: 10.8};

function buildScene() {
  const layers = new Map(), flows = [];
  const L = (key, o) => {
    if (!layers.has(key)) layers.set(key, {mesh: new Mesh(), c: o.c, e: o.e || 0, a: o.a ?? 1, pass: o.pass || 'opaque', asset: o.asset || null, dyn: o.dyn || null});
    return layers.get(key).mesh;
  };
  const flow = (pts, kv, spec) => {
    const cum = [0];
    for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + V.len(V.sub(pts[i], pts[i - 1])));
    flows.push({pts, cum, length: cum[cum.length - 1], kv, ...spec});
  };

  // Diorama slab: translucent ground so the cable network stays visible.
  const X0 = -96, X1 = 96, Z0 = -40, Z1 = 40, YB = -7;
  L('bottom', {c: C.bottom}).box(X0, YB - 0.3, Z0, X1, YB, Z1);
  const side = L('side', {c: C.side, a: 0.82, pass: 'ground'}), sc = [0, -3.5, 0];
  side.poly([[X0, YB, Z1], [X1, YB, Z1], [X1, 0, Z1], [X0, 0, Z1]], sc).poly([[X0, YB, Z0], [X1, YB, Z0], [X1, 0, Z0], [X0, 0, Z0]], sc)
    .poly([[X0, YB, Z0], [X0, YB, Z1], [X0, 0, Z1], [X0, 0, Z0]], sc).poly([[X1, YB, Z0], [X1, YB, Z1], [X1, 0, Z1], [X1, 0, Z0]], sc);
  const rim = L('rim', {c: C.rim, e: 0.35});
  for (const y of [0, YB]) rim.box(X0, y - 0.06, Z1 - 0.1, X1, y + 0.06, Z1).box(X0, y - 0.06, Z0, X1, y + 0.06, Z0 + 0.1).box(X0, y - 0.06, Z0, X0 + 0.1, y + 0.06, Z1).box(X1 - 0.1, y - 0.06, Z0, X1, y + 0.06, Z1);
  for (const x of [X0, X1]) for (const z of [Z0, Z1]) rim.box(x - 0.06, YB, z - 0.06, x + 0.06, 0, z + 0.06);
  const xs = [X0, -62, -14, -12, PIT.x0, PIT.x1, X1], zs = [Z0, -20, 7, PIT.z0, PIT.z1, 11, 18, 20, Z1];
  const surface = {ground: [C.ground, 0.86], yard: [C.yard, 0.88], walk: [C.walk, 0.82], pitcover: [C.walk, 0.82], road: [C.road, 0.9]};
  for (let i = 0; i < xs.length - 1; i++) for (let j = 0; j < zs.length - 1; j++) {
    const x0 = xs[i], x1 = xs[i + 1], z0 = zs[j], z1 = zs[j + 1], cx = (x0 + x1) / 2, cz = (z0 + z1) / 2;
    let type = 'ground';
    if (cx > -62 && cx < -14 && cz > -20 && cz < 20) type = 'yard';
    else if (cx > PIT.x0 && cx < PIT.x1 && cz > PIT.z0 && cz < PIT.z1) type = 'pitcover';
    else if (cx > -12 && ((cz > 7 && cz < 11) || (cz > 18 && cz < 20))) type = 'walk';
    else if (cx > -12 && cz > 11 && cz < 18) type = 'road';
    L('g:' + type, {c: surface[type][0], a: surface[type][1], pass: 'ground', dyn: type === 'pitcover' ? S => ({visible: !S.pit}) : null})
      .poly([[x0, 0, z0], [x1, 0, z0], [x1, 0, z1], [x0, 0, z1]], [cx, -1, cz]);
  }
  const mark = L('marking', {c: C.marking}), kerb = L('kerb', {c: C.kerb});
  for (let x = -10; x < 94; x += 5) mark.box(x, 0, 14.42, x + 2.4, 0.05, 14.58);
  kerb.box(-12, 0, 10.9, X1, 0.14, 11.05).box(-12, 0, 17.95, X1, 0.14, 18.1);

  // Excavation pit, shown once the faulted cable is isolated for the crew.
  const pitDyn = S => ({visible: S.pit}), pd = -2.3, pc = [(PIT.x0 + PIT.x1) / 2, -1.2, (PIT.z0 + PIT.z1) / 2];
  const pitWall = L('pitwall', {c: C.soil, asset: 'fault', dyn: pitDyn});
  const inward = pts => { const fc = V.mul(pts.reduce((s, p) => V.add(s, p), [0, 0, 0]), 1 / pts.length); pitWall.poly(pts, V.add(fc, V.sub(fc, pc))); };
  inward([[PIT.x0, 0, PIT.z0], [PIT.x0, 0, PIT.z1], [PIT.x0, pd, PIT.z1], [PIT.x0, pd, PIT.z0]]);
  inward([[PIT.x1, 0, PIT.z0], [PIT.x1, 0, PIT.z1], [PIT.x1, pd, PIT.z1], [PIT.x1, pd, PIT.z0]]);
  inward([[PIT.x0, 0, PIT.z0], [PIT.x1, 0, PIT.z0], [PIT.x1, pd, PIT.z0], [PIT.x0, pd, PIT.z0]]);
  inward([[PIT.x0, 0, PIT.z1], [PIT.x1, 0, PIT.z1], [PIT.x1, pd, PIT.z1], [PIT.x0, pd, PIT.z1]]);
  L('pitfloor', {c: C.sand, asset: 'fault', dyn: pitDyn}).poly([[PIT.x0, pd, PIT.z0], [PIT.x1, pd, PIT.z0], [PIT.x1, pd, PIT.z1], [PIT.x0, pd, PIT.z1]], [pc[0], pd - 1, pc[2]]);
  const barrier = L('barrier', {c: C.barrier, e: 0.35, asset: 'fault', dyn: pitDyn});
  const bx0 = PIT.x0 - 0.4, bx1 = PIT.x1 + 0.4, bz0 = PIT.z0 - 0.4, bz1 = PIT.z1 + 0.4;
  for (const [x, z] of [[bx0, bz0], [bx1, bz0], [bx0, bz1], [bx1, bz1]]) barrier.box(x - 0.07, 0, z - 0.07, x + 0.07, 1.1, z + 0.07);
  barrier.box(bx0, 0.95, bz0 - 0.04, bx1, 1.05, bz0 + 0.04).box(bx0, 0.95, bz1 - 0.04, bx1, 1.05, bz1 + 0.04).box(bx0 - 0.04, 0.95, bz0, bx0 + 0.04, 1.05, bz1).box(bx1 - 0.04, 0.95, bz0, bx1 + 0.04, 1.05, bz1);
  L('faultgem', {c: C.fault, e: 1, asset: 'fault', dyn: S => ({visible: Boolean(S.fault), e: 0.55 + 0.45 * S.pulse})}).gem([2, -1.4, 9.8], 0.55);
  L('beacon', {c: C.fault, a: 0.5, pass: 'glow', dyn: S => ({visible: Boolean(S.fault), a: 0.25 + 0.3 * S.pulse})}).prism([2, 0, 9.8], [2, 15, 9.8], 0.16, 8, 0.02, false);
  const ring = L('beaconring', {c: C.fault, a: 0.7, pass: 'glow', dyn: S => ({visible: Boolean(S.fault)})});
  for (let i = 0; i < 20; i++) {
    const a0 = (i / 20) * Math.PI * 2, a1 = ((i + 1) / 20) * Math.PI * 2;
    ring.prism([2 + Math.cos(a0) * 2, 0.08, 9.8 + Math.sin(a0) * 2], [2 + Math.cos(a1) * 2, 0.08, 9.8 + Math.sin(a1) * 2], 0.06, 4, 0.06, false);
  }

  // 01 Transmission: lattice tower and 132 kV conductors into the gantry.
  const tower = L('tower', {c: C.steel, asset: 'tower'}), T = {x: -80, z: 0, h: 20, b: 5, t: 1.4};
  const half = y => T.b / 2 + (T.t / 2 - T.b / 2) * (y / T.h), CN = [[-1, -1], [1, -1], [1, 1], [-1, 1]];
  const corner = (y, sx, sz) => [T.x + sx * half(y), y, T.z + sz * half(y)];
  const levels = [0, 3.5, 7, 10.5, 14, 17, 20];
  for (const [sx, sz] of CN) tower.prism(corner(0, sx, sz), corner(T.h, sx, sz), 0.13, 4);
  for (let k = 0; k < levels.length - 1; k++) for (let f = 0; f < 4; f++) {
    const [ax, az] = CN[f], [bx, bz] = CN[(f + 1) % 4], y0 = levels[k], y1 = levels[k + 1];
    tower.prism(corner(y0, ax, az), corner(y1, bx, bz), 0.055, 4).prism(corner(y0, bx, bz), corner(y1, ax, az), 0.055, 4).prism(corner(y1, ax, az), corner(y1, bx, bz), 0.06, 4);
  }
  for (const [sx, sz] of CN) tower.prism(corner(T.h, sx, sz), [T.x, 23.5, T.z], 0.08, 4);
  tower.box(T.x - 0.22, 14.82, -6.4, T.x + 0.22, 15.18, 6.4).box(T.x - 0.2, 18.84, -0.8, T.x + 0.2, 19.16, 4.4);
  for (const s of [-1, 1]) tower.prism([T.x, 16.6, s * 0.7], [T.x, 15.1, s * 6.2], 0.05, 4);
  tower.prism([T.x, 20.4, 0.6], [T.x, 19.1, 4.2], 0.05, 4);
  const insulator = L('porcelain', {c: C.porcelain});
  for (const [z, y0, y1] of [[-5.8, 14.82, 13.6], [5.8, 14.82, 13.6], [3.8, 18.84, 17.4]]) insulator.prism([T.x, y0, z], [T.x, y1, z], 0.17, 8);
  const hvLine = L('hv:line', {asset: 'tower', dyn: wire('B132', 132)});
  const phases = [[-5.8, 13.6, -5], [5.8, 13.6, 5], [3.8, 17.4, 0]];
  for (const [z, y, gz] of phases) {
    hvLine.tube(sag([X0, y, z], [T.x, y, z], 0.4, 8), 0.11).tube(sag([T.x, y, z], [-59.6, 14.2, gz], 0.7, 12), 0.11);
  }
  const earth = L('earthwire', {c: C.steel});
  earth.tube(sag([X0, 23.5, 0], [T.x, 23.5, 0], 0.3, 8), 0.04, 4).tube(sag([T.x, 23.5, 0], [-58, 16.6, 0], 0.5, 12), 0.04, 4);
  flow([[X0, 13.6, -5.8], [T.x, 13.6, -5.8], [-59.6, 14.2, -5], [-57.6, 14.2, -5], [-52.8, 8.2, -5]], 132, {branch: 'L1', a: 'SRC', b: 'B132'});
  flow([[X0, 13.6, 5.8], [T.x, 13.6, 5.8], [-59.6, 14.2, 5], [-57.6, 14.2, 5], [-51.2, 8.2, 5]], 132, {branch: 'L1', a: 'SRC', b: 'B132'});

  // 02 Grid station: gantry, 132 kV bus, bays, power transformers.
  const yard = L('yardsteel', {c: C.steel, asset: 'bus'});
  yard.box(-58.4, 0, -8.2, -57.6, 15, -7.4).box(-58.4, 0, 7.4, -57.6, 15, 8.2).box(-58.5, 14.4, -8.4, -57.5, 15.2, 8.4).prism([-58, 15.2, 0], [-58, 16.6, 0], 0.08, 4);
  for (const z of [-7.8, 7.8]) for (let y = 1; y < 14; y += 3) yard.prism([-58, y, z - 0.4], [-58, y + 3, z + 0.4], 0.04, 4).prism([-58, y, z + 0.4], [-58, y + 3, z - 0.4], 0.04, 4);
  const yardPorcelain = L('yardporcelain', {c: C.porcelain, asset: 'bus'});
  const busWire = L('hv:bus', {asset: 'bus', dyn: wire('B132', 132)});
  const busX = [-52.8, -52, -51.2];
  for (const [i, z] of [[0, -5], [1, 0], [2, 5]]) {
    yardPorcelain.prism([-58.4, 14.2, z], [-59.6, 14.2, z], 0.15, 8);
    busWire.tube(sag([-57.6, 14.2, z], [busX[i], 8.2, z], 0.8, 10), 0.08);
  }
  for (const x of busX) busWire.prism([x, 8.2, -12.5], [x, 8.2, 12.5], 0.11, 6);
  for (const z of [-11, -3.5, 3.5, 11]) {
    yard.box(-52.2, 0, z - 0.2, -51.8, 6.4, z + 0.2).box(-53.3, 6.2, z - 0.18, -50.7, 6.6, z + 0.18);
    for (const x of busX) yardPorcelain.prism([x, 6.6, z], [x, 8.05, z], 0.13, 8);
  }
  const tx = L('tank', {c: C.tank, asset: 'powertx'}), txDark = L('tankdark', {c: C.tankDark, asset: 'powertx'}), fins = L('fins', {c: C.fin, asset: 'powertx'});
  const txPorcelain = L('txporcelain', {c: C.porcelain, asset: 'powertx'}), plinth = L('plinth', {c: C.concrete, asset: 'powertx'});
  for (const [zb, cb, hvNode] of [[-8, 'CBT1', 'T1H'], [8, 'CBT2', 'T2H']]) {
    const bayB = L('hv:bay:' + zb, {asset: 'bus', dyn: wire('B132', 132)}), bayT = L('hv:tx:' + zb, {asset: 'bus', dyn: wire(hvNode, 132)});
    yard.box(-48.2, 0, zb - 1.6, -47.8, 4.8, zb - 1.2).box(-48.2, 0, zb + 1.2, -47.8, 4.8, zb + 1.6).box(-48.4, 4.6, zb - 1.7, -47.6, 5, zb + 1.7);
    yard.box(-43.2, 0, zb - 1.7, -42.8, 3, zb - 1.3).box(-43.2, 0, zb + 1.3, -42.8, 3, zb + 1.7).box(-43.4, 2.9, zb - 1.8, -42.6, 3.3, zb + 1.8);
    L('mechanism', {c: C.tankDark, asset: 'bus'}).box(-43.9, 1.2, zb - 0.5, -43.3, 2.4, zb + 0.5);
    L('cblamp:' + cb, {asset: 'bus', dyn: lampOf(cb)}).box(-43.75, 1.85, zb + 0.5, -43.45, 2.15, zb + 0.6);
    [-0.9, 0, 0.9].forEach((o, i) => {
      const z = zb + o;
      bayB.tube(sag([busX[i], 8.2, z], [-48.6, 6.35, z], 0.3, 6), 0.07);
      yardPorcelain.prism([-48.6, 5, z], [-48.6, 6.2, z], 0.11, 8).prism([-47.4, 5, z], [-47.4, 6.2, z], 0.11, 8);
      yard.box(-48.7, 6.2, z - 0.06, -47.3, 6.35, z + 0.06);
      bayB.tube(sag([-47.3, 6.35, z], [-43, 6.35, z], 0.15, 6), 0.07);
      L('interrupter', {c: hex('#9aa7b2'), asset: 'bus'}).prism([-43, 3.3, z], [-43, 6.1, z], 0.2, 10);
      yard.prism([-43, 6.1, z], [-43, 6.35, z], 0.26, 10);
      bayT.tube(sag([-43, 6.35, z], [-33.2, 7.25, z], 0.35, 10), 0.07);
      txPorcelain.prism([-33.2, 4.75, z], [-33.2, 7.2, z], 0.2, 8, 0.11);
    });
    flow([[-52, 8.2, zb], [-48, 6.35, zb], [-43, 6.35, zb], [-33.2, 7.25, zb]], 132, {branch: cb, a: 'B132', b: hvNode});
    plinth.box(-37, 0, zb - 3.2, -29, 0.6, zb + 3.2);
    tx.box(-36, 0.6, zb - 2.2, -30, 4.6, zb + 2.2);
    txDark.box(-36.15, 4.6, zb - 2.35, -29.85, 4.75, zb + 2.35).box(-30, 2.4, zb - 1, -29.3, 4, zb + 1);
    for (const s of [-1, 1]) {
      for (let k = 0; k < 8; k++) { const x = -35.5 + k * 0.66, za = zb + s * 2.2, zc = zb + s * 3.3; fins.box(x - 0.06, 1, Math.min(za, zc), x + 0.06, 4.2, Math.max(za, zc)); }
      txDark.prism([-35.8, 4.25, zb + s * 2.75], [-30.6, 4.25, zb + s * 2.75], 0.1, 6).prism([-35.8, 0.95, zb + s * 2.75], [-30.6, 0.95, zb + s * 2.75], 0.1, 6);
    }
    tx.prism([-35.3, 5.7, zb - 1.9], [-35.3, 5.7, zb + 1.9], 0.55, 12);
    txDark.box(-35.45, 4.75, zb - 1.3, -35.15, 5.2, zb - 1.1).box(-35.45, 4.75, zb + 1.1, -35.15, 5.2, zb + 1.3);
  }
  L('firewall', {c: hex('#4a5866'), asset: 'powertx'}).box(-37.5, 0, -0.35, -28.5, 5.8, 0.35);
  const t1l = [[-29.6, 2.4, -8], [-29.6, -1.0, -8], [-27.5, -1.0, -8], [-27.5, -1.0, panelZ('IC1')], [-22.6, -1.0, panelZ('IC1')], [-22.6, 0.15, panelZ('IC1')]];
  const t2l = [[-29.6, 2.4, 8], [-29.6, -1.25, 8], [-27.9, -1.25, 8], [-27.9, -1.25, panelZ('IC2')], [-22.6, -1.25, panelZ('IC2')], [-22.6, 0.15, panelZ('IC2')]];
  L('mv:t1l', {asset: 'powertx', dyn: wire('T1L', 11)}).tube(t1l, 0.15, 6);
  L('mv:t2l', {asset: 'powertx', dyn: wire('T2L', 11)}).tube(t2l, 0.15, 6);
  flow(t1l, 11, {branch: 'IC1', a: 'T1L', b: 'BA'});
  flow(t2l, 11, {branch: 'IC2', a: 'T2L', b: 'BB'});

  // 11 kV switchgear building, roof cut away to show the panel lineup.
  const sgWall = L('sgwall', {c: C.wall, asset: 'switchgear'});
  L('sgfloor', {c: C.floor, asset: 'switchgear'}).box(-26, 0, -14, -18, 0.15, 1);
  sgWall.box(-26, 0, -14, -25.65, 4, 1).box(-18.35, 0, -14, -18, 4, 1).box(-26, 0, -14, -18, 4, -13.65).box(-26, 0, 0.65, -18, 4, 1);
  for (const id of PANELS) {
    const zc = panelZ(id);
    L('panel', {c: C.panel, asset: 'switchgear'}).box(-23.2, 0.15, zc - 0.625, -22, 2.75, zc + 0.625);
    L('panellamp:' + id, {asset: 'switchgear', dyn: lampOf(id)}).box(-22, 2.15, zc - 0.16, -21.92, 2.47, zc + 0.16).box(-22.9, 2.75, zc - 0.26, -22.3, 2.81, zc + 0.26);
  }
  // Control room with operator console and video wall.
  const crWall = L('crwall', {c: C.wall, asset: 'control'});
  L('crfloor', {c: C.floor, asset: 'control'}).box(-26, 0, 3, -18, 0.15, 12);
  crWall.box(-26, 0, 3, -25.65, 3.4, 12).box(-18.35, 0, 3, -18, 3.4, 12).box(-26, 0, 3, -18, 3.4, 3.35).box(-26, 0, 11.65, -18, 3.4, 12);
  L('wallscreen', {c: C.wallscreen, e: 1, asset: 'control'}).box(-25.64, 0.9, 4.4, -25.52, 3, 10.6);
  const mimicLine = (c, key) => L('mimic:' + key, {c, e: 1, asset: 'control'});
  mimicLine(C.mv, 'mv').box(-25.52, 2.06, 5, -25.47, 2.14, 10);
  for (const z of [5.6, 6.8, 8.2, 9.4]) mimicLine(C.mv, 'mv').box(-25.52, 1.25, z - 0.04, -25.47, 2.06, z + 0.04);
  mimicLine(C.hv, 'hv').box(-25.52, 2.62, 6, -25.47, 2.7, 9).box(-25.52, 2.14, 7.46, -25.47, 2.62, 7.54);
  for (const [z, c] of [[5.6, C.red], [6.8, C.red], [8.2, C.green], [9.4, C.red]]) L('mimic:' + z, {c, e: 1, asset: 'control'}).box(-25.52, 1.55, z - 0.12, -25.46, 1.79, z + 0.12);
  L('desk', {c: C.desk, asset: 'control'}).box(-23.4, 0.15, 4.8, -22.4, 0.85, 10.2).box(-24.6, 0.15, 4.8, -23.4, 0.85, 5.4).box(-24.6, 0.15, 9.6, -23.4, 0.85, 10.2);
  L('desktop', {c: hex('#4a5968'), asset: 'control'}).box(-23.45, 0.85, 4.75, -22.35, 0.92, 10.25);
  for (const zc of [5.6, 6.9, 8.2, 9.5]) {
    L('monitor', {c: C.screen, e: 0.85, asset: 'control'}).box(-23.3, 1.0, zc - 0.55, -23.2, 1.72, zc + 0.55);
    L('stand', {c: C.chair, asset: 'control'}).box(-23.3, 0.92, zc - 0.08, -23.2, 1.0, zc + 0.08);
  }
  for (const zc of [6.3, 8.8]) L('chair', {c: C.chair, asset: 'control'}).box(-21.8, 0.15, zc - 0.32, -21.2, 0.6, zc + 0.32).box(-21.25, 0.6, zc - 0.32, -21.12, 1.25, zc + 0.32);

  // Station fence with a gate facing the road.
  const fence = L('fence', {c: C.fence});
  const post = (x, z) => fence.box(x - 0.07, 0, z - 0.07, x + 0.07, 2.4, z + 0.07);
  for (let x = -62; x <= -14; x += 4) { post(x, -20); post(x, 20); }
  for (let z = -16; z < 20; z += 4) { post(-62, z); if (z < 10 || z > 17) post(-14, z); }
  for (const y of [0.9, 1.6, 2.3]) {
    fence.box(-62, y - 0.025, -20.03, -14, y + 0.025, -19.97).box(-62, y - 0.025, 19.97, -14, y + 0.025, 20.03).box(-62.03, y - 0.025, -20, -61.97, y + 0.025, 20);
    fence.box(-14.03, y - 0.025, -20, -13.97, y + 0.025, 10).box(-14.03, y - 0.025, 17, -13.97, y + 0.025, 20);
  }

  // 03 Overhead network: feeder cable, riser pole, 11 kV line, PMTs, LT line and homes.
  const f1Cable = [[-22.6, 0.15, panelZ('F1')], [-22.6, -1.2, panelZ('F1')], [-10.4, -1.2, panelZ('F1')], [-10.4, -1.2, 8.2], [-8.5, -1.2, 8.2], [-8.5, 9.3, 8.2]];
  const riser = L('mv:riser', {asset: 'riser', dyn: wire('F1L', 11)});
  riser.tube(f1Cable, 0.15, 6);
  L('termination', {c: C.porcelain, asset: 'riser'}).prism([-8.5, 9.3, 8.2], [-8.5, 9.8, 8.2], 0.18, 6, 0.08);
  const poleXs = [-8, 6, 20, 34, 50], phase = [[0, 11.4], [-1.3, 10.5], [1.3, 10.5]];
  for (const [dz, h] of phase) riser.tube([[-8.5, 9.8, 8.2], [-8, h, 8.2 + dz]], 0.05, 4);
  flow(f1Cable, 11, {branch: 'F1', a: 'BA', b: 'F1L'});
  const poleMesh = L('pole', {c: C.concrete, asset: 'overhead'}), arms = L('arms', {c: C.steel, asset: 'overhead'}), pins = L('pins', {c: C.porcelain, asset: 'overhead'});
  const pole = (x, z, h = 11) => poleMesh.prism([x, 0, z], [x, h, z], 0.24, 8, 0.15);
  for (const x of poleXs) {
    pole(x, 8.2, x === 50 ? 10 : 11);
    arms.box(x - 0.08, 9.9, 6.6, x + 0.08, 10.1, 9.8);
    if (x !== 50) { pins.prism([x, 10.1, 6.9], [x, 10.45, 6.9], 0.08, 6).prism([x, 10.1, 9.5], [x, 10.45, 9.5], 0.08, 6).prism([x, 11, 8.2], [x, 11.35, 8.2], 0.08, 6); }
  }
  const mvLine = L('mv:line', {asset: 'overhead', dyn: wire('F1L', 11)});
  for (let i = 0; i < poleXs.length - 1; i++) for (const [dz, h] of phase) {
    const x0 = poleXs[i], x1 = poleXs[i + 1], end = x1 === 50 ? [49.4, 10.6, 8.2 + dz] : [x1, h, 8.2 + dz];
    mvLine.tube(sag([x0, h, 8.2 + dz], end, 0.35, 10), 0.075, 5);
  }
  flow([[-8, 11.4, 8.2], [6, 11.4, 8.2], [20, 11.4, 8.2], [34, 11.4, 8.2], [49.4, 10.6, 8.2]], 11, {node: 'F1L', entries: {F1: 'start', ABS: 'end'}});
  // F1 continues south from pole 20 to the rest of its network.
  for (const z of [23.5, 35]) { pole(20, z); arms.box(18.6, 9.9, z - 0.08, 21.4, 10.1, z + 0.08); pins.prism([18.9, 10.1, z], [18.9, 10.45, z], 0.08, 6).prism([21.1, 10.1, z], [21.1, 10.45, z], 0.08, 6).prism([20, 11, z], [20, 11.35, z], 0.08, 6); }
  arms.box(18.6, 9.2, 8.12, 21.4, 9.36, 8.28);
  for (const [dx, h0, h] of [[-1.1, 9.5, 10.5], [1.1, 9.5, 10.5], [0, 11.4, 11.4]]) {
    mvLine.tube(sag([20 + dx, h0, 8.2], [20 + dx, h, 23.5], 0.35, 10), 0.075, 5).tube(sag([20 + dx, h, 23.5], [20 + dx, h, 35], 0.3, 10), 0.075, 5).tube(sag([20 + dx, h, 35], [20 + dx, h, Z1], 0.2, 6), 0.075, 5);
  }
  flow([[20, 11.4, 8.2], [20, 11.4, 23.5], [20, 11.4, 35], [20, 11.4, Z1]], 11, {node: 'F1L', entries: {F1: 'start', ABS: 'start'}});
  // Street lights on the line poles.
  for (const x of [-8, 6, 20, 34]) {
    arms.prism([x, 7.6, 8.4], [x, 7.9, 10.6], 0.05, 4);
    L('streetlamp', {asset: 'overhead', dyn: S => S.on('F1L') ? {c: C.lamp, e: 1} : {c: C.winOff, e: 0}}).box(x - 0.3, 7.55, 10.35, x + 0.3, 7.8, 10.95);
  }
  // Pole mounted transformers PMT-1 and PMT-2.
  for (const x of [6, 34]) {
    const pmt = L('pmt', {c: hex('#8795a2'), asset: 'pmt'}), pmtDark = L('pmtdark', {c: C.tankDark, asset: 'pmt'});
    pmt.box(x - 0.6, 7.0, 6.75, x + 0.6, 8.4, 7.9);
    pmtDark.box(x - 0.5, 7.2, 6.5, x + 0.5, 8.2, 6.75).box(x - 0.65, 8.4, 6.7, x + 0.65, 8.5, 7.95).box(x - 0.1, 7.4, 7.9, x + 0.1, 7.6, 8.05).box(x - 0.8, 9.35, 7.2, x + 0.8, 9.45, 7.35).box(x - 0.05, 9.35, 7.3, x + 0.05, 9.45, 8.05);
    const leads = L('mv:pmt', {asset: 'pmt', dyn: wire('F1L', 11)});
    [[-0.6, [x + 0.3, 10.5, 6.9]], [0, [x + 0.3, 11.35, 8.2]], [0.6, [x + 0.3, 10.5, 9.5]]].forEach(([dx, top]) => {
      L('fuse', {c: C.porcelain, asset: 'pmt'}).prism([x + dx, 9.45, 7.28], [x + dx + 0.1, 10, 7.28], 0.05, 6);
      L('bushing', {c: C.porcelain, asset: 'pmt'}).prism([x + dx * 0.6, 8.5, 7.3], [x + dx * 0.6, 8.9, 7.3], 0.06, 6);
      leads.tube([[x + dx + 0.1, 10, 7.28], top], 0.035, 4).tube([[x + dx, 9.45, 7.28], [x + dx * 0.6, 8.9, 7.3]], 0.035, 4);
    });
    L('lv:pmt', {asset: 'pmt', dyn: wire('F1L', 0.4)}).tube([[x + 0.4, 7.0, 7.4], [x + 0.4, 6.3, 7.4]], 0.05, 4);
  }
  const lt = L('lv:line', {asset: 'community', dyn: wire('F1L', 0.4)});
  for (const x of poleXs) arms.box(x - 0.07, 6.0, 6.8, x + 0.07, 6.15, 9.6);
  for (let i = 0; i < poleXs.length - 1; i++) for (const z of [7.0, 7.6, 8.8, 9.4]) lt.tube(sag([poleXs[i], 6.25, z], [poleXs[i + 1], 6.25, z], 0.25, 8), 0.04, 4);
  // Houses: north front row with service drops, a back row, and a row across the road.
  const houseTones = ['house0', 'house1', 'house2'];
  const house = (xc, z0, z1, h, k, windowsOn) => {
    L('house:' + houseTones[k % 3], {c: C[houseTones[k % 3]], asset: 'community'}).box(xc - 3, 0, z0, xc + 3, h, z1);
    L('roof:' + (k % 2), {c: k % 2 ? C.roof2 : C.roof, asset: 'community'}).gable(xc - 3.3, z0 - 0.3, xc + 3.3, z1 + 0.3, h, h + 1.9);
    for (const face of windowsOn) {
      const zf = face === 'south' ? z1 : z0 - 0.08;
      for (const dx of [-2, 0.8]) L('win:F1L', {asset: 'community', dyn: lights('F1L')}).box(xc + dx, 1.3, zf, xc + dx + 1.2, 2.3, zf + 0.08);
    }
    L('door', {c: C.door, asset: 'community'}).box(xc - 0.5, 0, windowsOn[0] === 'south' ? z1 : z0 - 0.06, xc + 0.3, 1.9, windowsOn[0] === 'south' ? z1 + 0.06 : z0);
  };
  [-3, 5, 13, 23, 31, 41].forEach((xc, k) => {
    house(xc, -3.5, 2, 3.2 + (k % 3) * 0.25, k, ['south']);
    const xp = poleXs.reduce((best, x) => Math.abs(x - xc) < Math.abs(best - xc) ? x : best, poleXs[0]);
    lt.tube(sag([xp, 6.25, 7.0], [xc, 3.0, 2.04], 0.4, 8), 0.035, 4);
  });
  [-2, 7, 15, 24, 33, 42].forEach((xc, k) => house(xc, -12, -6.5, 3.3 + ((k + 1) % 3) * 0.25, k + 1, ['south']));
  [-3, 8, 29, 39, 45].forEach((xc, k) => house(xc, 21.5, 27, 3.2 + ((k + 2) % 3) * 0.25, k + 2, ['north', 'south']));

  // ABS tie on the end pole, riser and tie cable to RMU-1.
  const absClosed = L('abs:closed', {c: C.steel, asset: 'abs', dyn: S => ({visible: S.closed('ABS')})});
  const absOpen = L('abs:open', {c: C.steel, asset: 'abs', dyn: S => ({visible: !S.closed('ABS')})});
  const absTie = L('mv:tie', {asset: 'abs', dyn: wire('TIE', 11)});
  for (const z of [6.9, 8.2, 9.5]) {
    L('abspins', {c: C.porcelain, asset: 'abs'}).prism([49.4, 10.1, z], [49.4, 10.55, z], 0.08, 6).prism([50.6, 10.1, z], [50.6, 10.55, z], 0.08, 6);
    absClosed.box(49.4, 10.55, z - 0.05, 50.6, 10.65, z + 0.05);
    absOpen.prism([49.4, 10.6, z], [50.09, 11.58, z], 0.05, 4);
    absTie.tube([[50.6, 10.55, z], [50.45, 9.4, 8.95]], 0.04, 4);
  }
  L('absrod', {c: C.steel, asset: 'abs'}).prism([50.25, 10.05, 8.55], [50.25, 1.2, 8.55], 0.03, 4).box(50.15, 1, 8.45, 50.6, 1.25, 8.65).prism([50, 10, 8.2], [50, 11.9, 8.2], 0.03, 4);
  L('abslamp', {asset: 'abs', dyn: lampOf('ABS')}).box(49.82, 11.9, 8.02, 50.18, 12.26, 8.38);
  L('absterm', {c: C.porcelain, asset: 'abs'}).prism([50.45, 9.0, 8.95], [50.45, 9.4, 8.95], 0.16, 6, 0.07);
  const tie = [[50.45, 9.0, 8.95], [50.45, -1.1, 8.95], [55.7, -1.1, 8.95], [55.7, -1.1, 8.2], [55.7, 0.15, 8.2]];
  absTie.tube(tie, 0.15, 6);
  flow(tie, 11, {branch: 'RS3', a: 'TIE', b: 'R1'});

  // 04 Underground network: cable C1 with joints and the fault, RMU-1, compact substation.
  const c1 = [[-22.6, 0.15, panelZ('F2')], [-22.6, -1.4, panelZ('F2')], [-12.2, -1.4, panelZ('F2')], [-12.2, -1.4, 9.8], [55.0, -1.4, 9.8], [55.0, -1.4, 8.0], [55.0, 0.15, 8.0]];
  L('mv:c1', {asset: 'cable', dyn: S => S.fault && !S.on('F2C') ? {c: C.fault, e: 0.35} : wire('F2C', 11)(S)}).tube(c1, 0.17, 6);
  for (const x of [12, 34]) L('joint', {c: C.joint, asset: 'cable'}).prism([x - 0.8, -1.4, 9.8], [x + 0.8, -1.4, 9.8], 0.34, 8);
  for (const x of [-6, 8, 18, 28, 42]) L('marker', {c: C.marker, asset: 'cable'}).box(x - 0.15, 0, 10.45, x + 0.15, 0.22, 10.75);
  flow(c1, 11, {branch: 'F2', a: 'BB', b: 'F2C'});
  L('rmubase', {c: C.concrete, asset: 'rmu'}).box(54.4, 0, 7.0, 57.6, 0.15, 8.8);
  L('rmu', {c: C.rmu, asset: 'rmu'}).box(54.6, 0.15, 7.2, 57.4, 1.9, 8.6).box(54.5, 1.9, 7.1, 57.5, 2.0, 8.7);
  L('rmuantenna', {c: C.steel, asset: 'rmu'}).prism([57.2, 2.0, 7.4], [57.2, 3.1, 7.4], 0.03, 4);
  ['RS1', 'RS2', 'RS3', 'TF1'].forEach((id, k) => L('rmulamp:' + id, {asset: 'rmu', dyn: lampOf(id)}).box(54.85 + k * 0.68, 1.35, 8.6, 55.15 + k * 0.68, 1.65, 8.68));
  const cssLink = [[56.4, 0.15, 7.6], [56.4, -1.0, 7.6], [56.4, -1.0, 4.0], [61.0, -1.0, 4.0], [61.0, 0.15, 4.0]];
  L('mv:css', {asset: 'kiosk', dyn: wire('CSS', 11)}).tube(cssLink, 0.15, 6);
  flow(cssLink, 11, {branch: 'TF1', a: 'R1', b: 'CSS'});
  L('cssbase', {c: C.concrete, asset: 'kiosk'}).box(59.7, 0, 2.1, 64.8, 0.15, 5.9);
  L('css', {c: C.css, asset: 'kiosk'}).box(60, 0.15, 2.4, 64.5, 2.8, 5.6);
  L('cssroof', {c: C.roof, asset: 'kiosk'}).box(59.8, 2.8, 2.2, 64.7, 3.05, 5.8);
  for (let k = 0; k < 5; k++) L('louver', {c: C.tankDark, asset: 'kiosk'}).box(62.6, 0.8 + k * 0.35, 5.6, 64.1, 0.92 + k * 0.35, 5.66);
  L('cssdoor', {c: hex('#56636f'), asset: 'kiosk'}).box(60.3, 0.3, 5.6, 62.2, 2.5, 5.64);
  L('csslamp', {asset: 'kiosk', dyn: S => S.on('CSS') ? {c: C.lamp, e: 1} : {c: C.winOff, e: 0}}).box(60.5, 2.5, 5.6, 60.8, 2.68, 5.68);
  // Apartments and market on underground LT supply.
  const windows = (key, dyn, x0, x1, z0, z1, floors, faces, asset) => {
    const m = L('win:' + key, {asset, dyn}), off = L('winoff:' + key, {c: C.winOff, asset});
    for (let f = 0; f < floors; f++) for (const face of faces) {
      const along = face === 'south' || face === 'north' ? [x0, x1] : [z0, z1], span = along[1] - along[0];
      const n = Math.floor((span - 0.6) / 1.9), start = along[0] + (span - (n * 1.9 - 0.8)) / 2;
      for (let c = 0; c < n; c++) {
        const a = start + c * 1.9, y = 1.4 + f * 2.8, target = (f * 3 + c * 2 + face.length) % 7 === 0 ? off : m;
        if (face === 'south') target.box(a, y, z1, a + 1.1, y + 1.2, z1 + 0.08);
        if (face === 'north') target.box(a, y, z0 - 0.08, a + 1.1, y + 1.2, z0);
        if (face === 'east') target.box(x1, y, a, x1 + 0.08, y + 1.2, a + 1.1);
        if (face === 'west') target.box(x0 - 0.08, y, a, x0, y + 1.2, a + 1.1);
      }
    }
  };
  L('apartment', {c: C.wall2, asset: 'commercial'}).box(68, 0, -6, 78, 18, 4).box(67.8, 18, -6.2, 78.2, 18.5, 4.2);
  L('tanks', {c: C.tankDark, asset: 'commercial'}).prism([70.5, 18.5, -2.5], [70.5, 19.8, -2.5], 0.6, 10).prism([72.3, 18.5, -2.5], [72.3, 19.8, -2.5], 0.6, 10);
  windows('apt', lights('CSS'), 68, 78, -6, 4, 6, ['south', 'east', 'west'], 'commercial');
  L('market', {c: C.house1, asset: 'commercial'}).box(82, 0, -4, 94, 4.6, 5).box(81.8, 4.6, -4.2, 94.2, 4.85, 5.2);
  L('awning', {c: C.awning, asset: 'commercial'}).poly([[82, 3.7, 5], [94, 3.7, 5], [94, 3.1, 6.8], [82, 3.1, 6.8]], [88, 2, 5.9]).poly([[82, 3.62, 5], [94, 3.62, 5], [94, 3.02, 6.8], [82, 3.02, 6.8]], [88, 5, 5.9]).box(82, 2.95, 6.72, 94, 3.12, 6.86);
  for (let k = 0; k < 4; k++) L('shop', {asset: 'commercial', dyn: lights('CSS')}).box(82.6 + k * 2.9, 0.5, 5, 84.9 + k * 2.9, 2.7, 5.08);
  L('sign', {asset: 'commercial', dyn: S => S.on('CSS') ? {c: C.sign, e: 1} : {c: C.winOff, e: 0}}).box(82.4, 3.95, 5, 93.6, 4.4, 5.08);
  const ltApt = [[63.8, 0.15, 3.2], [63.8, -0.9, 3.2], [69, -0.9, 3.2], [69, 0.15, 3.2]];
  const ltMarket = [[64.2, 0.15, 3.0], [64.2, -0.8, 3.0], [83, -0.8, 3.0], [83, 0.15, 3.0]];
  L('lv:css', {asset: 'commercial', dyn: wire('CSS', 0.4)}).tube(ltApt, 0.12, 5).tube(ltMarket, 0.12, 5);
  flow(ltApt, 0.4, {node: 'CSS', entries: {TF1: 'start'}});
  flow(ltMarket, 0.4, {node: 'CSS', entries: {TF1: 'start'}});
  // Ring onward: cable C2 to RMU-2 and the area it supplies.
  const c2a = [[57.1, 0.15, 8.4], [57.1, -1.3, 8.4], [57.1, -1.3, 10.4], [66, -1.3, 10.4], [66, -1.3, 19.3], [69.0, -1.3, 19.3], [69.0, 0.15, 19.3]];
  const c2b = [[70.8, 0.15, 19.3], [70.8, -1.3, 19.3], [X1, -1.3, 19.3]];
  L('mv:c2', {asset: 'ring', dyn: wire('C2', 11)}).tube(c2a, 0.16, 6).tube(c2b, 0.16, 6);
  flow(c2a, 11, {branch: 'RS2', a: 'R1', b: 'C2'});
  flow(c2b, 11, {node: 'C2', entries: {RS2: 'start', NO6: 'end'}});
  L('rmu2', {c: C.rmu, asset: 'ring'}).box(68.6, 0.15, 18.6, 71.4, 1.9, 19.9).box(68.5, 1.9, 18.5, 71.5, 2.0, 20.0);
  L('rmu2base', {c: C.concrete, asset: 'ring'}).box(68.4, 0, 18.4, 71.6, 0.15, 20.1);
  for (const [x0, x1, z0, z1, h, tone] of [[64, 72, 23, 31, 8, 'house2'], [75, 84, 22, 33, 12, 'wall2'], [87, 94, 24, 32, 6, 'house1']]) {
    L('ringbldg:' + tone, {c: C[tone], asset: 'ring'}).box(x0, 0, z0, x1, h, z1).box(x0 - 0.2, h, z0 - 0.2, x1 + 0.2, h + 0.4, z1 + 0.2);
    windows('ring', lights('C2'), x0, x1, z0, z1, Math.floor((h - 0.6) / 2.8), ['south', 'north', 'east'], 'ring');
  }
  // Feeders F3 to F6 leave the station northward to the rest of the network.
  [['F3', 'F3L'], ['F5', 'F5L'], ['F4', 'F4L'], ['F6', 'F6L']].forEach(([id, node], k) => {
    const z = panelZ(id), x = -17.2 + k * 0.7, route = [[-22.6, 0.15, z], [-22.6, -0.7, z], [x, -0.7, z], [x, -0.7, Z0]];
    L('mv:' + id, {asset: 'feeders', dyn: wire(node, 11)}).tube(route, 0.13, 5);
    flow(route, 11, {branch: id, a: id === 'F3' || id === 'F5' ? 'BA' : 'BB', b: node});
  });
  // Trees for scale.
  for (const [x, z, s] of [[-4, -17, 1], [7, -18.5, 1.2], [18, -17, 0.9], [29, -18, 1.1], [41, -17.5, 1], [53, -16, 1.2], [60, -11, 0.9], [85, -13, 1.1], [92, -21, 1], [-70, 26, 1.3], [-86, -24, 1.2], [-70, -31, 1], [48, 31, 1.1], [56, 36, 0.9], [-6, 34, 1.2], [9, 36, 1], [-88, 30, 1.1], [30, 33, 1]]) {
    L('trunk', {c: C.trunk}).prism([x, 0, z], [x, 1.3 * s, z], 0.13 * s, 5);
    L('leaf', {c: C.leaf}).prism([x, 1.0 * s, z], [x, 4.2 * s, z], 1.25 * s, 7, 0.06);
  }
  return {layers: [...layers.values()], flows};
}

const VS = 'attribute vec3 aPos;attribute vec3 aNrm;uniform mat4 uVP;varying vec3 vN;varying vec3 vW;void main(){vN=aNrm;vW=aPos;gl_Position=uVP*vec4(aPos,1.0);}';
const FS = 'precision mediump float;varying vec3 vN;varying vec3 vW;uniform vec3 uColor;uniform float uEmit;uniform float uAlpha;uniform float uHi;uniform vec3 uEye;uniform vec3 uFog;uniform vec2 uFogRange;uniform vec3 uLight;' +
  'void main(){vec3 n=normalize(vN);float diff=max(dot(n,uLight),0.0);float hemi=0.5+0.5*n.y;vec3 c=uColor*(0.34+0.2*hemi+0.62*diff);c=mix(c,uColor*1.12,uEmit);' +
  'c=mix(c,vec3(0.41,0.89,0.76),uHi*0.32)+uHi*0.04;float d=distance(vW,uEye);float f=clamp((d-uFogRange.x)/(uFogRange.y-uFogRange.x),0.0,1.0);c=mix(c,uFog,f*0.8);gl_FragColor=vec4(c,uAlpha);}';
const PVS = 'attribute vec3 aPos;uniform mat4 uVP;uniform float uSize;void main(){gl_Position=uVP*vec4(aPos,1.0);gl_PointSize=clamp(uSize/gl_Position.w,2.5,26.0);}';
const PFS = 'precision mediump float;uniform vec3 uColor;uniform float uAlpha;void main(){vec2 p=gl_PointCoord-vec2(0.5);float r=dot(p,p)*4.0;if(r>1.0)discard;float a=(1.0-r)*(1.0-r)*uAlpha;gl_FragColor=vec4(uColor*a,a);}';
const KVS = 'attribute vec3 aPos;uniform mat4 uVP;void main(){gl_Position=uVP*vec4(aPos,1.0);}';
const KFS = 'precision mediump float;uniform vec3 uId;void main(){gl_FragColor=vec4(uId,1.0);}';

const VIEWS = {
  overview: {target: [0, 0, 0], dist: 178, yaw: 0.3, pitch: 0.56, fit: true},
  station: {target: [-40, 3, 0], dist: 72, yaw: 0.62, pitch: 0.5},
  control: {target: [-22, 1.2, 7], dist: 30, yaw: 0.85, pitch: 0.95},
  overhead: {target: [18, 5, 8], dist: 66, yaw: 0.28, pitch: 0.36},
  underground: {target: [26, -1.2, 9], dist: 74, yaw: 0.12, pitch: 0.5, xray: true},
  customers: {target: [76, 3, 6], dist: 70, yaw: -0.18, pitch: 0.66}
};
const DEVICE_FOCUS = {
  CBT1: {target: [-43, 3, -8], dist: 34}, CBT2: {target: [-43, 3, 8], dist: 34},
  IC1: {target: [-22.6, 1.5, -7], dist: 30}, IC2: {target: [-22.6, 1.5, -7], dist: 30}, BC: {target: [-22.6, 1.5, -7], dist: 30},
  F1: {target: [-22.6, 1.5, -7], dist: 30}, F2: {target: [-22.6, 1.5, -7], dist: 30}, F3: {target: [-22.6, 1.5, -7], dist: 30},
  F4: {target: [-22.6, 1.5, -7], dist: 30}, F5: {target: [-22.6, 1.5, -7], dist: 30}, F6: {target: [-22.6, 1.5, -7], dist: 30},
  RS1: {target: [56, 1, 8], dist: 24}, RS2: {target: [56, 1, 8], dist: 24}, RS3: {target: [56, 1, 8], dist: 24}, TF1: {target: [56, 1, 8], dist: 24},
  ABS: {target: [50, 9, 8.2], dist: 26}, NO6: {target: [80, 3, 24], dist: 56}
};
const LABELS = [
  {t: 'Fault on C1', p: [2, 3.2, 9.8], cls: 'fault', show: S => Boolean(S.fault)},
  {t: '132 kV line', p: [-80, 24.8, 0]},
  {t: 'T1', p: [-33, 8.4, -8]},
  {t: 'T2', p: [-33, 8.4, 8]},
  {t: '11 kV switchgear', p: [-22, 5.2, -8]},
  {t: 'Control room', p: [-22, 4.4, 7.5]},
  {t: 'F1 overhead feeder', p: [13, 12.9, 8.2]},
  {t: 'ABS tie', p: [50, 13.4, 8.2], state: S => S.closed('ABS') ? 'closed' : 'open'},
  {t: 'RMU 1', p: [56, 3.5, 7.9]},
  {t: 'Compact substation', p: [62.2, 4.6, 4]},
  {t: 'Apartments', p: [73, 20.3, -1]},
  {t: 'Market', p: [88, 6.4, 0.5]},
  {t: 'RMU 2 to 6', p: [70, 3.6, 19.3]},
  {t: 'F2 cable C1', p: [24, -1.4, 9.8], cls: 'under'},
  {t: 'PMT 1', p: [6, 6.6, 6.2], minor: true},
  {t: 'PMT 2', p: [34, 6.6, 6.2], minor: true},
  {t: 'Feeders F3 to F6', p: [-15.5, -0.7, -30], cls: 'under', minor: true},
  {t: 'F1 network continues', p: [20, 12.8, 36], minor: true}
];

function createTwin(canvas, overlay, hooks) {
  let gl = null;
  try { gl = canvas.getContext('webgl', {antialias: true, alpha: false}); } catch { gl = null; }
  if (!gl) return null;
  const compile = (type, src) => {
    const s = gl.createShader(type);
    gl.shaderSource(s, src); gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) throw Error(gl.getShaderInfoLog(s));
    return s;
  };
  const program = (vs, fs, attributes) => {
    const p = gl.createProgram();
    gl.attachShader(p, compile(gl.VERTEX_SHADER, vs)); gl.attachShader(p, compile(gl.FRAGMENT_SHADER, fs));
    attributes.forEach((a, i) => gl.bindAttribLocation(p, i, a));
    gl.linkProgram(p);
    if (!gl.getProgramParameter(p, gl.LINK_STATUS)) throw Error(gl.getProgramInfoLog(p));
    const u = {};
    for (let i = 0; i < gl.getProgramParameter(p, gl.ACTIVE_UNIFORMS); i++) { const info = gl.getActiveUniform(p, i); u[info.name] = gl.getUniformLocation(p, info.name); }
    return {p, u};
  };
  const main = program(VS, FS, ['aPos', 'aNrm']), points = program(PVS, PFS, ['aPos']), pick = program(KVS, KFS, ['aPos']);
  const scene = buildScene();
  for (const l of scene.layers) {
    const data = new Float32Array(l.mesh.v);
    l.count = data.length / 6; l.buf = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, l.buf); gl.bufferData(gl.ARRAY_BUFFER, data, gl.STATIC_DRAW);
    l.mesh = null;
  }
  const assetList = [...new Set(scene.layers.map(l => l.asset).filter(Boolean))];
  const particleBuf = gl.createBuffer();
  const cam = {...VIEWS.overview, target: [...VIEWS.overview.target]};
  let goal = null, S = null, selected = null, xray = false, flowOn = true, labelsOn = true, running = false, visible = true, raf = 0, last = 0, clock = 0, dirty = true, pickFbo = null;
  const labelEls = LABELS.map(lb => { const el = document.createElement('span'); el.className = 'cr-label' + (lb.cls ? ' ' + lb.cls : ''); overlay.appendChild(el); return el; });

  const eyeOf = c => [c.target[0] + c.dist * Math.cos(c.pitch) * Math.sin(c.yaw), c.target[1] + c.dist * Math.sin(c.pitch), c.target[2] + c.dist * Math.cos(c.pitch) * Math.cos(c.yaw)];
  const eye = () => eyeOf(cam);
  const FOV = 38 * Math.PI / 180;
  let autoFit = true;
  // Frame the whole diorama for the current panel shape: steeper and closer on tall panels.
  function fitted(v) {
    const aspect = canvas.clientWidth / Math.max(1, canvas.clientHeight), t = Math.tan(FOV / 2);
    const pitch = aspect < 1.1 ? 0.85 : aspect < 1.6 ? 0.66 : v.pitch, pts = [[-80, 24, 0]];
    for (const x of [-96, 96]) for (const z of [-40, 40]) for (const y of [-7, 0]) pts.push([x, y, z]);
    let lo = 30, hi = 600;
    for (let i = 0; i < 26; i++) {
      const d = (lo + hi) / 2, e = eyeOf({...v, pitch, dist: d});
      const f = V.norm(V.sub(v.target, e)), r = V.norm(V.cross(f, [0, 1, 0])), u = V.cross(r, f);
      const fits = pts.every(pt => { const q = V.sub(pt, e), z = V.dot(q, f); return z > 0 && Math.abs(V.dot(q, r) / (z * t * aspect)) < 0.95 && Math.abs(V.dot(q, u) / (z * t)) < 0.9; });
      if (fits) hi = d; else lo = d;
    }
    return {...v, pitch, dist: hi};
  }
  function matrices() {
    const e = eye(), aspect = canvas.width / Math.max(1, canvas.height);
    const proj = perspective(FOV, aspect, Math.max(0.5, cam.dist * 0.02), cam.dist * 6 + 240);
    return {e, vp: multiply(proj, lookAt(e, cam.target, [0, 1, 0]))};
  }
  function resize() {
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const w = Math.max(1, Math.round(canvas.clientWidth * dpr)), h = Math.max(1, Math.round(canvas.clientHeight * dpr));
    if (canvas.width !== w || canvas.height !== h) {
      canvas.width = w; canvas.height = h; pickFbo = null; dirty = true;
      if (autoFit && !goal) Object.assign(cam, fitted(VIEWS.overview), {target: [...VIEWS.overview.target]});
    }
  }
  function look(l) {
    const d = l.dyn ? l.dyn(S) : null;
    if (d && d.visible === false) return null;
    return {c: d && d.c || l.c, e: d && d.e != null ? d.e : l.e, a: d && d.a != null ? d.a : l.a};
  }
  function drawLayers(pass, vp, e) {
    for (const l of scene.layers) {
      if (l.pass !== pass) continue;
      const m = look(l);
      if (!m) continue;
      gl.uniform3fv(main.u.uColor, m.c); gl.uniform1f(main.u.uEmit, m.e);
      gl.uniform1f(main.u.uAlpha, pass === 'ground' ? m.a * (xray ? 0.34 : 1) : m.a);
      gl.uniform1f(main.u.uHi, selected && l.asset === selected ? 1 : 0);
      gl.bindBuffer(gl.ARRAY_BUFFER, l.buf);
      gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 24, 0); gl.vertexAttribPointer(1, 3, gl.FLOAT, false, 24, 12);
      gl.drawArrays(gl.TRIANGLES, 0, l.count);
    }
  }
  function pointAt(f, s) {
    let i = 1;
    while (i < f.cum.length - 1 && f.cum[i] < s) i++;
    const seg = f.cum[i] - f.cum[i - 1] || 1;
    return V.lerp(f.pts[i - 1], f.pts[i], (s - f.cum[i - 1]) / seg);
  }
  function direction(f) {
    if (f.branch) {
      const fl = S.flows[f.branch];
      if (!fl || fl.amps < 0.5) return 0;
      return fl.from === f.a ? 1 : fl.from === f.b ? -1 : 0;
    }
    if (!S.on(f.node) || !(S.load[f.node] > 0)) return 0;
    const p = S.parent[f.node], side = p && f.entries[p.branch];
    return side === 'start' ? 1 : side === 'end' ? -1 : 0;
  }
  function drawParticles(vp, underground, pixelScale) {
    if (!flowOn) return;
    const groups = {132: [], 11: [], 0.4: []}, speed = reducedMotion() ? 0 : 7, spacing = 3.6;
    for (const f of scene.flows) {
      const dir = direction(f);
      if (!dir) continue;
      const offset = (clock * speed) % spacing;
      for (let s0 = offset; s0 < f.length; s0 += spacing) {
        const p = pointAt(f, dir > 0 ? s0 : f.length - s0);
        if ((p[1] < -0.05) === underground) groups[f.kv].push(p[0], p[1], p[2]);
      }
    }
    gl.useProgram(points.p); gl.disableVertexAttribArray(1);
    gl.uniformMatrix4fv(points.u.uVP, false, vp);
    gl.bindBuffer(gl.ARRAY_BUFFER, particleBuf);
    for (const [kv, arr] of Object.entries(groups)) {
      if (!arr.length) continue;
      const color = kv === '132' ? C.hv : kv === '11' ? C.mv : C.lv;
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(arr), gl.DYNAMIC_DRAW);
      gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 12, 0);
      gl.uniform3fv(points.u.uColor, [Math.min(1, color[0] * 1.2), Math.min(1, color[1] * 1.2), Math.min(1, color[2] * 1.2)]);
      gl.uniform1f(points.u.uAlpha, underground ? (xray ? 0.95 : 0.6) : 1);
      gl.uniform1f(points.u.uSize, (kv === '132' ? 0.95 : kv === '11' ? 0.8 : 0.6) * pixelScale);
      gl.drawArrays(gl.POINTS, 0, arr.length / 3);
    }
    gl.useProgram(main.p); gl.enableVertexAttribArray(1);
  }
  function draw() {
    resize();
    const {e, vp} = matrices();
    gl.viewport(0, 0, canvas.width, canvas.height);
    gl.clearColor(C.bg[0], C.bg[1], C.bg[2], 1);
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    gl.enable(gl.DEPTH_TEST); gl.depthFunc(gl.LEQUAL); gl.disable(gl.CULL_FACE);
    gl.useProgram(main.p); gl.enableVertexAttribArray(0); gl.enableVertexAttribArray(1);
    gl.uniformMatrix4fv(main.u.uVP, false, vp); gl.uniform3fv(main.u.uEye, e); gl.uniform3fv(main.u.uFog, C.bg);
    gl.uniform2f(main.u.uFogRange, cam.dist * 1.0, cam.dist * 3.4); gl.uniform3fv(main.u.uLight, V.norm([-0.45, 0.8, 0.55]));
    gl.disable(gl.BLEND); gl.depthMask(true);
    drawLayers('opaque', vp, e);
    const pixelScale = canvas.height / (2 * Math.tan(FOV / 2));
    gl.enable(gl.BLEND); gl.depthMask(false); gl.blendFunc(gl.ONE, gl.ONE);
    drawParticles(vp, true, pixelScale);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    drawLayers('ground', vp, e);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE);
    drawLayers('glow', vp, e);
    gl.blendFunc(gl.ONE, gl.ONE);
    drawParticles(vp, false, pixelScale);
    gl.depthMask(true); gl.disable(gl.BLEND);
    placeLabels(vp);
  }
  function placeLabels(vp) {
    const w = canvas.clientWidth, h = canvas.clientHeight, placed = [];
    LABELS.forEach((lb, i) => {
      const el = labelEls[i];
      const show = labelsOn && (!lb.show || lb.show(S)) && (!lb.minor || cam.dist < 120) && (lb.cls !== 'under' || xray || cam.dist < 110);
      if (!show) { el.hidden = true; return; }
      const [x, y, z] = lb.p;
      const cw = vp[3] * x + vp[7] * y + vp[11] * z + vp[15];
      if (cw <= 0.1) { el.hidden = true; return; }
      const sx = ((vp[0] * x + vp[4] * y + vp[8] * z + vp[12]) / cw * 0.5 + 0.5) * w;
      const sy = (1 - ((vp[1] * x + vp[5] * y + vp[9] * z + vp[13]) / cw * 0.5 + 0.5)) * h;
      const text = lb.state ? `${lb.t} · ${lb.state(S)}` : lb.t;
      const bw = text.length * 6.4 + 16, bh = 22, box = [sx - bw / 2, sy - bh - 4, sx + bw / 2, sy - 4];
      if (box[0] < 4 || box[2] > w - 4 || box[1] < 44 || sy > h - 24 || placed.some(o => box[0] < o[2] && box[2] > o[0] && box[1] < o[3] && box[3] > o[1])) { el.hidden = true; return; }
      placed.push(box);
      if (el.textContent !== text) el.textContent = text;
      el.hidden = false;
      el.style.transform = `translate(${Math.round(sx)}px,${Math.round(sy - 6)}px) translate(-50%,-100%)`;
    });
  }
  function frame(now) {
    raf = 0;
    if (!running || !visible) return;
    const dt = Math.min(0.05, (now - (last || now)) / 1000);
    last = now;
    if (!reducedMotion()) clock += dt;
    if (goal) {
      const k = reducedMotion() ? 1 : 1 - Math.exp(-dt * 5);
      cam.yaw += (goal.yaw - cam.yaw) * k; cam.pitch += (goal.pitch - cam.pitch) * k; cam.dist += (goal.dist - cam.dist) * k;
      cam.target = V.lerp(cam.target, goal.target, k);
      if (Math.abs(goal.dist - cam.dist) < 0.05 && V.len(V.sub(goal.target, cam.target)) < 0.05 && Math.abs(goal.yaw - cam.yaw) < 0.002) { Object.assign(cam, goal, {target: [...goal.target]}); goal = null; }
      dirty = true;
    }
    const animating = !reducedMotion() && (flowOn || (S && S.fault));
    if (dirty || animating) {
      if (S) { S.pulse = 0.5 + 0.5 * Math.sin(clock * 4); draw(); }
      dirty = false;
    }
    raf = requestAnimationFrame(frame);
  }
  function kick() { if (running && visible && !raf) { last = 0; raf = requestAnimationFrame(frame); } }
  function flyTo(g) {
    const yaw = g.yaw ?? cam.yaw, delta = Math.atan2(Math.sin(yaw - cam.yaw), Math.cos(yaw - cam.yaw));
    goal = {yaw: cam.yaw + delta, pitch: g.pitch ?? Math.max(cam.pitch, 0.42), dist: g.dist ?? cam.dist, target: [...(g.target || cam.target)]};
    dirty = true; kick();
  }
  function pan(dx, dy) {
    const k = cam.dist * 0.0017, s = Math.sin(cam.yaw), c = Math.cos(cam.yaw);
    cam.target = [clamp(cam.target[0] - c * dx * k - s * dy * k, -96, 96), cam.target[1], clamp(cam.target[2] + s * dx * k - c * dy * k, -40, 40)];
  }
  const zoomBy = f => { cam.dist = clamp(cam.dist * f, 16, 600); goal = null; autoFit = false; dirty = true; kick(); };
  function ensurePickTarget() {
    if (pickFbo) return;
    const tex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, tex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, canvas.width, canvas.height, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
    const depth = gl.createRenderbuffer();
    gl.bindRenderbuffer(gl.RENDERBUFFER, depth);
    gl.renderbufferStorage(gl.RENDERBUFFER, gl.DEPTH_COMPONENT16, canvas.width, canvas.height);
    pickFbo = gl.createFramebuffer();
    gl.bindFramebuffer(gl.FRAMEBUFFER, pickFbo);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, tex, 0);
    gl.framebufferRenderbuffer(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.RENDERBUFFER, depth);
    gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  }
  function pickAt(clientX, clientY) {
    resize(); ensurePickTarget();
    const rect = canvas.getBoundingClientRect();
    const x = Math.floor((clientX - rect.left) / rect.width * canvas.width), y = Math.floor((1 - (clientY - rect.top) / rect.height) * canvas.height);
    const {vp} = matrices();
    gl.bindFramebuffer(gl.FRAMEBUFFER, pickFbo);
    gl.viewport(0, 0, canvas.width, canvas.height);
    gl.clearColor(0, 0, 0, 1); gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    gl.disable(gl.BLEND); gl.enable(gl.DEPTH_TEST); gl.depthMask(true);
    gl.useProgram(pick.p); gl.disableVertexAttribArray(1); gl.uniformMatrix4fv(pick.u.uVP, false, vp);
    for (const l of scene.layers) {
      if (l.pass === 'glow' || (l.pass === 'ground' && xray) || !look(l)) continue;
      const id = l.asset ? assetList.indexOf(l.asset) + 1 : 0;
      gl.uniform3f(pick.u.uId, id / 255, 0, 0);
      gl.bindBuffer(gl.ARRAY_BUFFER, l.buf); gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 24, 0);
      gl.drawArrays(gl.TRIANGLES, 0, l.count);
    }
    const px = new Uint8Array(4);
    gl.readPixels(clamp(x, 0, canvas.width - 1), clamp(y, 0, canvas.height - 1), 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, px);
    gl.bindFramebuffer(gl.FRAMEBUFFER, null);
    selected = px[0] ? assetList[px[0] - 1] : null;
    dirty = true; kick();
    hooks.onPick(selected);
  }

  // Pointer, touch and keyboard controls.
  const pointers = new Map();
  let drag = null, pinch = 0;
  canvas.addEventListener('pointerdown', e => {
    canvas.setPointerCapture(e.pointerId);
    pointers.set(e.pointerId, {x: e.clientX, y: e.clientY});
    drag = {pan: e.button === 2 || e.shiftKey, moved: 0};
    canvas.classList.add('dragging');
  });
  canvas.addEventListener('pointermove', e => {
    if (!pointers.has(e.pointerId) || !drag) return;
    const prev = pointers.get(e.pointerId);
    pointers.set(e.pointerId, {x: e.clientX, y: e.clientY});
    if (pointers.size === 2) {
      const [a, b] = [...pointers.values()], d = Math.hypot(a.x - b.x, a.y - b.y);
      if (pinch) zoomBy(pinch / d);
      pinch = d; drag.moved += 10;
      return;
    }
    const dx = e.clientX - prev.x, dy = e.clientY - prev.y;
    drag.moved += Math.abs(dx) + Math.abs(dy);
    goal = null; autoFit = false;
    if (drag.pan) pan(dx, dy);
    else { cam.yaw -= dx * 0.006; cam.pitch = clamp(cam.pitch + dy * 0.005, 0.08, 1.45); }
    dirty = true; kick();
  });
  const release = e => {
    if (!pointers.has(e.pointerId)) return;
    pointers.delete(e.pointerId);
    if (pointers.size < 2) pinch = 0;
    if (pointers.size === 0) {
      if (drag && drag.moved < 6 && e.type === 'pointerup') pickAt(e.clientX, e.clientY);
      drag = null; canvas.classList.remove('dragging');
    }
  };
  canvas.addEventListener('pointerup', release);
  canvas.addEventListener('pointercancel', release);
  canvas.addEventListener('contextmenu', e => e.preventDefault());
  canvas.addEventListener('wheel', e => { if (e.ctrlKey || e.metaKey) { e.preventDefault(); zoomBy(Math.exp(e.deltaY * 0.0015)); } }, {passive: false});
  canvas.addEventListener('keydown', e => {
    const step = {ArrowLeft: [0.08, 0], ArrowRight: [-0.08, 0], ArrowUp: [0, 0.05], ArrowDown: [0, -0.05]}[e.key];
    if (step) { e.preventDefault(); goal = null; autoFit = false; cam.yaw += step[0]; cam.pitch = clamp(cam.pitch + step[1], 0.08, 1.45); dirty = true; kick(); }
    if (e.key === '+' || e.key === '=') zoomBy(0.85);
    if (e.key === '-') zoomBy(1.18);
  });
  const io = new IntersectionObserver(entries => { visible = entries.some(en => en.isIntersecting); if (visible) { dirty = true; kick(); } });
  io.observe(canvas);
  document.addEventListener('visibilitychange', () => { visible = !document.hidden; if (visible) { dirty = true; kick(); } });
  window.addEventListener('resize', () => { dirty = true; kick(); });

  return {
    setState(next) { S = {...next, pulse: S ? S.pulse : 1}; dirty = true; kick(); },
    view(name) { const v = VIEWS[name]; if (!v) return; xray = Boolean(v.xray); hooks.onXray(xray); autoFit = Boolean(v.fit); flyTo(v.fit ? fitted(v) : v); },
    focus(device) { const f = DEVICE_FOCUS[device]; if (f) { autoFit = false; flyTo({...f, pitch: 0.5}); } },
    select(asset) { selected = asset; dirty = true; kick(); },
    setXray(on) { xray = on; dirty = true; kick(); },
    setFlow(on) { flowOn = on; dirty = true; kick(); },
    setLabels(on) { labelsOn = on; dirty = true; kick(); },
    zoom: zoomBy,
    resume() { running = true; dirty = true; kick(); },
    pause() { running = false; if (raf) cancelAnimationFrame(raf); raf = 0; }
  };
}

// Control room view

// Component descriptions shared by the supply network diagram, the 3D inspector and host pages.
export const NET_ASSETS = {
  tower:{tag:'01 · TRANSMISSION',title:'132 kV transmission line',rating:'132 kV · lattice steel towers · strain insulators',text:'Bulk power arrives from generation on 132 kV overhead circuits and terminates on the grid station gantry.',work:['Upstream of my area. The station supply set the limit for every 11 kV feeder I monitored and every load transfer I planned.']},
  bus:{tag:'02 · GRID STATION',title:'132 kV switchyard',rating:'Busbar · isolators · SF6 circuit breakers',text:'Each power transformer connects to the 132 kV busbar through an isolator and a circuit breaker. The breaker clears faults; the isolator gives a visible break for maintenance.',work:[]},
  powertx:{tag:'02 · GRID STATION',title:'Power transformers T1 and T2',rating:'132/11 kV · 40 MVA each, ONAN/ONAF (typical)',text:'Step the supply down from 132 kV to 11 kV. Each unit runs below half its rating, so either one can carry the whole station through the bus coupler while the other is out for maintenance.',work:['Checked transformer loading against rating before moving feeder load between sources.']},
  switchgear:{tag:'02 · GRID STATION',title:'11 kV switchgear and control room',rating:'Indoor panels · feeder breakers · overcurrent and earth fault relays',text:'The 11 kV busbar divides the station output into outgoing feeders. Every feeder breaker has protection relays, and each trip record is the starting point for fault finding.',work:['Monitored 11 kV feeder loading and trip events.','Coordinated load transfer between feeders during faults and planned shutdowns.']},
  overhead:{tag:'03 · OVERHEAD NETWORK',title:'11 kV overhead feeder F-1',rating:'Concrete poles · pin insulators · ACSR conductors',text:'Carries 11 kV along the streets. Overhead lines are quick to patrol and repair, but they are exposed to wind, birds, tree contact and kite strings.',work:['Troubleshot feeder trips and line faults with the field team.','Ran preventive maintenance patrols on poles, insulators and conductors.','Applied isolation and earthing procedures before any crew worked on the line.']},
  riser:{tag:'03 · OVERHEAD NETWORK',title:'Cable riser pole',rating:'11 kV outdoor terminations · lightning arresters',text:'The station cable climbs the first pole and joins the overhead conductors through outdoor terminations. Surge arresters protect the cable from lightning.',work:[]},
  pmt:{tag:'03 · OVERHEAD NETWORK',title:'Pole mounted transformer PMT 1',rating:'11/0.4 kV · 200 kVA · drop out fuses',text:'Steps 11 kV down to 400 V three phase for the neighbourhood. Drop out fuses disconnect the transformer from the line if it develops a fault.',work:['Carried out three phase testing and load readings on distribution transformers.','Redistributed load between transformers to keep each unit within its rating.']},
  community:{tag:'03 · OVERHEAD NETWORK',title:'Residential community on LT supply',rating:'400 V three phase · 230 V single phase service',text:'The low tension line runs below the 11 kV conductors and feeds each house through a service drop. Houses are spread across phases A, B and C.',work:['Balanced phases by moving single phase connections, so no phase of the transformer carried more than its share.']},
  abs:{tag:'03 · OVERHEAD NETWORK',title:'Normally open tie point',rating:'11 kV air break switch · N/O',text:'Links the overhead feeder to the underground ring. It stays open in normal operation. Closing it lets one feeder pick up the other feeder\'s customers while a faulted section is isolated.',work:['Performed load transfer between feeders to restore customers during faults and maintenance.']},
  cable:{tag:'04 · UNDERGROUND NETWORK',title:'11 kV underground feeder F-2',rating:'XLPE cable · direct buried · straight through joints',text:'Supplies the dense area where overhead lines are not practical. The cable is protected from weather, but its faults are hidden and must be located before any excavation.',work:['Localized underground cable faults and supervised repairs through to restoration.']},
  fault:{tag:'04 · UNDERGROUND NETWORK',title:'Cable fault localization',rating:'Insulation test · TDR prelocation · surge pinpointing',text:'Isolate and earth the faulted section. Insulation resistance tests identify the faulted core. A TDR gives the distance along the cable, route tracing follows its path, and a surge generator with acoustic pinpointing marks the spot to excavate. The new joint is pressure tested before the section is energized again.',work:['Located underground cable faults and coordinated the field team from excavation to jointing and restoration.']},
  rmu:{tag:'04 · UNDERGROUND NETWORK',title:'Ring main unit',rating:'11 kV · 4 way · three ring switches and a fused tee',text:'Switching point on the cable ring. Its ways take feeder F-2 in, carry the ring on to RMU 2 to 6, link to the overhead tie point, and feed the compact substation through a fused switch. Any cable section can be isolated and fed from the other side.',work:['Used ring switching to isolate faulted sections and transfer load.']},
  kiosk:{tag:'04 · UNDERGROUND NETWORK',title:'Compact substation',rating:'11/0.4 kV · 500 kVA · package unit',text:'A ground mounted transformer, 11 kV switch and LT distribution board in one enclosure. It suits dense areas supplied by underground cable.',work:['Carried out preventive maintenance and loading checks on distribution transformers.']},
  commercial:{tag:'04 · UNDERGROUND NETWORK',title:'Apartments and commercial market',rating:'400 V underground LT cables',text:'Multi storey residential blocks and shops take supply through underground LT cables from the compact substation distribution board.',work:[]}
};

const EXTRA_ASSETS = {
  control: {tag: '02 · GRID STATION', title: 'Control room', rating: 'SCADA workstations · video wall mimic', text: 'Operators watch feeder loading and alarms, and switch remote breakers and RMUs. Field operations are carried out by crews on the control room instruction.'},
  ring: {tag: '04 · UNDERGROUND NETWORK', title: 'Ring onward: RMU 2 to 6', rating: 'Cable C2 · 2.72 MW · 2,100 customers', text: 'The rest of the F2 cable ring. Its far end at RMU-6 has a normally open point to feeder F4, so this group can be fed from either side.'},
  feeders: {tag: '02 · GRID STATION', title: 'Feeders F3 to F6', rating: '11 kV cables to other areas · 15.5 MW', text: 'The station\'s other outgoing feeders. They share the 11 kV bus sections with F1 and F2.'}
};

export function mountControlRoom(root, {scada, assets = NET_ASSETS, header = true}) {
  const engine = createEngine(scada);
  const check = engine.verify(scada.references);
  const startClock = 14 * 60;
  const sim = {states: engine.normal(), fault: null, clock: startClock, cmi: 0, events: [], selected: null, command: null, drill: false, picked: null, follow: true};
  const deviceLabel = id => engine.byId[id].label;

  root.innerHTML = `${header ? `
    <div class="case-header"><div><div class="eyebrow">CONTROL ROOM · SCADA AND 3D DIGITAL TWIN</div><h2>Operate the network from the control room.</h2>
      <p>The supply network as a live 3D model beside a SCADA single line diagram. Select a switch, preview what it will do, then execute it. Run the cable fault drill to isolate the faulted cable and restore every customer by load transfer, the core of my feeder work at K-Electric.</p></div>
      <div class="voltage-ladder cr-check"><div><i class="lv-dot"></i><strong class="mono">${check.match}/${check.total}</strong><span>Python reference states matched</span></div><div><i class="mv-dot"></i><strong class="mono">${scada.drillResult.restoredAt}</strong><span>Best restoration time</span></div><div><i class="hv-dot"></i><strong class="mono">${fmtInt(scada.drillResult.customerMinutes)}</strong><span>Best customer minutes</span></div></div></div>` : ''}
    <div class="cr-hmi" id="cr-hmi" aria-live="polite"></div>
    <div class="cr-grid">
      <div class="cr-col">
      <section class="cr-twin" aria-label="3D digital twin of the network">
        <canvas id="cr-canvas" tabindex="0" aria-label="3D model. Drag to orbit, right drag or shift drag to pan, Ctrl and scroll or pinch to zoom. Arrow keys orbit."></canvas>
        <div class="cr-overlay" id="cr-overlay" aria-hidden="true"></div>
        <div class="cr-views" role="group" aria-label="Camera views">${[['overview', 'Overview'], ['station', 'Grid station'], ['control', 'Control room'], ['overhead', 'Overhead'], ['underground', 'Underground'], ['customers', 'Customers']].map(([v, l]) => `<button data-view3d="${v}">${l}</button>`).join('')}</div>
        <div class="cr-toggles"><button id="cr-xray" aria-pressed="false">X-ray ground</button><button id="cr-flow" aria-pressed="true">Power flow</button><button id="cr-labels" aria-pressed="true">Labels</button><button id="cr-zoomin" aria-label="Zoom in"><svg viewBox="0 0 12 12" aria-hidden="true"><path d="M2 6H10M6 2V10"/></svg></button><button id="cr-zoomout" aria-label="Zoom out"><svg viewBox="0 0 12 12" aria-hidden="true"><path d="M2 6H10"/></svg></button></div>
        <p class="cr-hint">Drag to orbit · right drag to pan · Ctrl + scroll to zoom · click to inspect</p>
        <div class="cr-info" id="cr-info" hidden></div>
        <div class="cr-nogl" id="cr-nogl" hidden><strong>3D view unavailable</strong><span>This browser did not provide WebGL. The SCADA simulator works without it.</span></div>
      </section>
      <section class="cr-drill" id="cr-drill"></section>
      </div>
      <div class="cr-col">
      <section class="cr-mimic" aria-label="SCADA single line diagram">
        <div class="cr-mimic-head"><span class="eyebrow">SCADA · GS-1 SINGLE LINE</span><label class="cr-follow"><input type="checkbox" id="cr-follow" checked> Camera follows selection</label></div>
        <div class="cr-mimic-scroll"><div id="cr-mimic"></div></div>
        <div class="cr-command" id="cr-command"></div>
      </section>
      <section class="cr-events"><div class="panel-title"><h3>Alarms and events</h3><button class="quiet" id="cr-ack">Acknowledge all</button></div><ol id="cr-events" class="cr-event-list"></ol></section>
      </div>
    </div>
    ${header ? `<p class="cr-foot small muted">Representative network drawn from my field experience. Loads, ratings and switching times are typical values for an urban 11 kV network, not K-Electric records. The browser switching engine recomputed ${check.total} reference states from the Python model and matched ${check.match}.</p>` : ''}`;

  const $ = s => root.querySelector(s);
  const canvas = $('#cr-canvas');
  let twin = null;
  try {
    twin = createTwin(canvas, $('#cr-overlay'), {
      onPick: asset => { sim.picked = asset; if (asset === 'abs') select('ABS', false); renderInfo(); },
      onXray: on => { $('#cr-xray').setAttribute('aria-pressed', String(on)); }
    });
  } catch (error) { twin = null; console.error(error); }
  if (!twin) { $('#cr-nogl').hidden = false; canvas.hidden = true; root.querySelectorAll('.cr-views,.cr-toggles,.cr-hint').forEach(el => { el.hidden = true; }); }

  const analysis = () => engine.analyze(sim.states, sim.fault);
  const log = (sev, dev, text) => { sim.events.unshift({time: clockText(sim.clock), sev, dev, text, ack: sev !== 'alarm'}); sim.events.length = Math.min(sim.events.length, 60); };
  const pct = (a, limit) => Math.round(a / limit * 100);

  function snapshot(A) {
    return {on: n => A.energized.has(n), closed: id => Boolean(sim.states[id]), fault: sim.fault, flows: A.flows, parent: A.parent, load: A.load,
      pit: Boolean(sim.fault) && !A.energized.has('F2C') && !sim.states.RS1 && !sim.states.F2};
  }

  function renderHmi(A) {
    const alarms = sim.events.filter(e => e.sev === 'alarm' && !e.ack).length;
    $('#cr-hmi').innerHTML = `<span class="cr-live"><i></i>SIMULATION</span><span>GS-1 · 132/11 kV</span><span>Time <b>${clockText(sim.clock)}</b></span><span>Load served <b>${A.mwServed.toFixed(2)} MW</b></span>
      <span class="${A.customersOff ? 'cr-bad' : ''}">Customers off supply <b>${fmtInt(A.customersOff)}</b></span><span>Customer minutes lost <b>${fmtInt(sim.cmi)}</b></span>
      ${Object.entries(A.flows).some(([id, f]) => engine.byId[id].limitA && f.amps > engine.byId[id].limitA) ? '<span class="cr-bad"><b>Overload</b></span>' : ''}<span class="cr-alarm ${alarms ? 'on' : ''}">${alarms ? `${alarms} unacknowledged alarm${alarms > 1 ? 's' : ''}` : 'No active alarms'}</span>`;
  }

  function renderMimic(A) {
    const on = n => A.energized.has(n);
    const col = n => on(n) ? (scada.nodes[n].kv > 100 ? '#7eaaff' : '#f4b76b') : '#4d5b69';
    const seg = (n, d, cable) => `<path d="${d}" stroke="${n === 'F2C' && sim.fault && !on(n) ? '#f48787' : col(n)}" class="m-line${cable ? ' m-cable' : ''}"/>`;
    const bus = (n, d) => `<path d="${d}" stroke="${col(n)}" class="m-bus"/>`;
    const amps = id => A.flows[id] ? A.flows[id].amps : 0;
    const device = (id, shape, x, y) => {
      const closed = sim.states[id], b = engine.byId[id], sel = sim.selected === id;
      const body = shape === 'breaker' ? `<rect x="${x - 8}" y="${y - 8}" width="16" height="16" class="${closed ? 'm-closed' : 'm-open'}"/>`
        : shape === 'fuse' ? `<rect x="${x - 5}" y="${y - 9}" width="10" height="18" class="${closed ? 'm-closed' : 'm-open'}"/><path d="M${x} ${y - 9}V${y + 9}" class="m-fuseline"/>`
        : `<circle cx="${x}" cy="${y}" r="7.5" class="${closed ? 'm-closed' : 'm-open'}"/>`;
      return `<g class="m-dev" data-dev="${id}" tabindex="0" role="button" aria-pressed="${sel}" aria-label="${esc(b.label)}, ${closed ? 'closed' : 'open'}, ${b.control === 'field' ? 'field operated' : 'remote'}"><rect class="m-hit" x="${x - 13}" y="${y - 13}" width="26" height="26"/>${body}${sel ? `<rect class="m-sel" x="${x - 12}" y="${y - 12}" width="24" height="24"/>` : ''}</g>`;
    };
    const tx = (x, y, top, bottom, r = 12, gap = 16) => `<circle cx="${x}" cy="${y}" r="${r}" class="m-wind" stroke="${top}"/><circle cx="${x}" cy="${y + gap}" r="${r}" class="m-wind" stroke="${bottom}"/>`;
    const arrow = (x, y, n) => `<path d="M${x - 5} ${y}L${x + 5} ${y}L${x} ${y + 8}Z" fill="${col(n)}"/>`;
    const load = id => {
      const f = A.flows[id], limit = engine.byId[id].limitA, a = f ? f.amps : 0, p = limit ? pct(a, limit) : 0;
      return {a, p, cls: p > 100 ? 'm-over' : p > 90 ? 'm-warn' : ''};
    };
    const feederLabel = (id, x) => { const l = load(id); return `<text x="${x + 13}" y="231" class="m-name">${id}</text><text x="${x + 13}" y="245" class="m-val ${l.cls}">${l.a.toFixed(1)} A</text>`; };
    const lv = n => on(n) ? '#68e3c2' : '#4d5b69';
    const t1 = A.flows.T1 ? A.flows.T1.mw / scada.pf : 0, t2 = A.flows.T2 ? A.flows.T2.mw / scada.pf : 0;
    const f1 = load('F1'), f4 = load('F4');
    $('#cr-mimic').innerHTML = `<svg viewBox="0 0 640 600" class="cr-mimic-svg" role="group" aria-label="SCADA single line diagram of grid station GS-1 and feeders F1, F2 and F4">
      <text x="14" y="20" class="m-title">GS-1 GRID STATION · 132/11 kV</text><text x="14" y="300" class="m-title">11 kV DISTRIBUTION</text>
      ${seg('B132', 'M320 28V60')}<text x="330" y="38" class="m-name">L1 132 kV</text><text x="330" y="52" class="m-val">${amps('L1').toFixed(1)} A</text>
      ${bus('B132', 'M150 60H490')}<text x="144" y="64" text-anchor="end" class="m-name">132 kV BUS</text>
      ${[[200, 'CBT1', 'T1H', 'T1L', 'IC1', 'BA', 'T1', t1], [440, 'CBT2', 'T2H', 'T2L', 'IC2', 'BB', 'T2', t2]].map(([x, cb, hv, lvN, ic, busN, name, mva]) => `
        ${seg('B132', `M${x} 60V78`)}${seg(hv, `M${x} 94V112`)}${tx(x, 124, col(hv), col(lvN))}${seg(lvN, `M${x} 152V170`)}${seg(busN, `M${x} 186V208`)}
        ${device(cb, 'breaker', x, 86)}${device(ic, 'breaker', x, 178)}
        <text x="${x - 14}" y="90" text-anchor="end" class="m-name">${cb === 'CBT1' ? 'CB-T1' : 'CB-T2'}</text><text x="${x - 14}" y="182" text-anchor="end" class="m-name">${ic === 'IC1' ? 'IC-1' : 'IC-2'}</text>
        <text x="${x + 18}" y="128" class="m-name">${name} 40 MVA</text><text x="${x + 18}" y="142" class="m-val ${pct(mva, 40) > 90 ? 'm-warn' : ''}">${mva.toFixed(1)} MVA · ${pct(mva, 40)}%</text>`).join('')}
      ${bus('BA', 'M60 208H300')}${seg('BA', 'M300 208H312')}${device('BC', 'breaker', 320, 208)}${seg('BB', 'M328 208H340')}${bus('BB', 'M340 208H580')}
      <text x="320" y="192" text-anchor="middle" class="m-name">BC</text>
      <text x="56" y="212" text-anchor="end" class="m-name">BUS A</text><text x="56" y="226" text-anchor="end" class="m-val">${on('BA') ? '11.0' : '0.0'} kV</text>
      <text x="584" y="212" class="m-name">BUS B</text><text x="584" y="226" class="m-val">${on('BB') ? '11.0' : '0.0'} kV</text>
      ${[['F1', 100, 'BA'], ['F3', 170, 'BA'], ['F5', 240, 'BA'], ['F2', 380, 'BB'], ['F6', 470, 'BB'], ['F4', 560, 'BB']].map(([id, x, busN]) => `${seg(busN, `M${x} 208V226`)}${device(id, 'breaker', x, 234)}${feederLabel(id, x)}`).join('')}
      ${[['F3', 170, 'F3L', '4.2 MW'], ['F5', 240, 'F5L', '3.9 MW'], ['F6', 470, 'F6L', '4.0 MW']].map(([id, x, n, mw]) => `${seg(n, `M${x} 242V262`)}${arrow(x, 262, n)}<text x="${x}" y="284" text-anchor="middle" class="m-val">${mw}</text>`).join('')}
      ${seg('F1L', 'M100 242V320H300')}<text x="112" y="312" class="m-name">F1 OVERHEAD · LIMIT 350 A</text>
      ${seg('F1L', 'M140 320V334')}${arrow(140, 334, 'F1L')}<text x="140" y="356" text-anchor="middle" class="m-val">F1 network</text><text x="140" y="368" text-anchor="middle" class="m-val">3.37 MW</text>
      ${[[200, 'PMT-1', '200 kVA'], [260, 'PMT-2', '100 kVA']].map(([x, n, r]) => `${seg('F1L', `M${x} 320V332`)}${tx(x, 338, col('F1L'), lv('F1L'), 6, 10)}<text x="${x}" y="368" text-anchor="middle" class="m-val">${n}</text><text x="${x}" y="380" text-anchor="middle" class="m-val">${r}</text>`).join('')}
      ${device('ABS', 'switch', 309, 320)}<text x="309" y="306" text-anchor="middle" class="m-name">ABS</text><text x="309" y="342" text-anchor="middle" class="m-val">field</text>
      ${seg('TIE', 'M317 320H350')}${seg('TIE', 'M350 320V392', true)}<text x="344" y="364" text-anchor="end" class="m-val">TIE</text>
      ${device('RS3', 'switch', 350, 401)}<text x="338" y="405" text-anchor="end" class="m-name">RS-3</text>${seg('R1', 'M350 410V430')}
      ${seg('F2C', 'M380 242V392', true)}<text x="388" y="300" class="m-val">C1 cable</text>
      ${sim.fault ? `<path d="M372 318l14 6l-10 4l14 8" class="m-fault"/><text x="398" y="330" class="m-over">FAULT</text>` : ''}
      ${device('RS1', 'switch', 380, 401)}<text x="392" y="405" class="m-name">RS-1</text><text x="392" y="419" class="m-val">${sim.fault ? 'FPI clear' : 'FPI'}</text>${seg('R1', 'M380 410V430')}
      ${bus('R1', 'M330 430H450')}<text x="456" y="434" class="m-name">RMU-1</text>
      ${seg('R1', 'M360 430V440')}${device('TF1', 'fuse', 360, 449)}${seg('CSS', 'M360 458V468')}${tx(360, 474, col('CSS'), lv('CSS'), 6, 10)}${seg('CSS', 'M360 490V496', false)}${arrow(360, 496, 'CSS')}
      <text x="346" y="474" text-anchor="end" class="m-name">CSS-1 500 kVA</text><text x="346" y="488" text-anchor="end" class="m-val">Apartments, market</text><text x="346" y="502" text-anchor="end" class="m-val">0.38 MW · 420 cust.</text>
      ${seg('R1', 'M430 430V440')}${device('RS2', 'switch', 430, 449)}<text x="442" y="453" class="m-name">RS-2</text>${seg('C2', 'M430 458V520', true)}
      <rect x="400" y="520" width="80" height="30" class="m-box" stroke="${col('C2')}"/><text x="440" y="533" text-anchor="middle" class="m-name">RMU 2 to 6</text><text x="440" y="545" text-anchor="middle" class="m-val">2.72 MW</text>
      ${seg('C2', 'M480 535H497')}${device('NO6', 'switch', 505, 535)}<text x="505" y="521" text-anchor="middle" class="m-name">N/O RMU-6</text>${seg('F4L', 'M513 535H560')}
      ${seg('F4L', 'M560 242V535', true)}${seg('F4L', 'M560 300H578')}<path d="M578 295L586 300L578 305Z" fill="${col('F4L')}"/><text x="590" y="304" class="m-val">3.4 MW</text>
      <text x="112" y="396" class="m-val ${f1.cls}">F1 ${f1.p}% of limit</text><text x="572" y="330" class="m-val ${f4.cls}">F4 ${f4.p}%</text>
      <g class="m-legend" transform="translate(14 572)"><rect x="0" y="-9" width="11" height="11" class="m-closed"/><text x="16" y="1">closed</text><rect x="66" y="-9" width="11" height="11" class="m-open"/><text x="82" y="1">open</text>
        <circle cx="136" cy="-3.5" r="5.5" class="m-closed"/><text x="146" y="1">switch</text><path d="M196 -3.5H222" class="m-line m-cable" stroke="#f4b76b"/><text x="228" y="1">cable</text>
        <path d="M270 -3.5H292" class="m-line" stroke="#7eaaff"/><text x="298" y="1">132 kV</text><path d="M346 -3.5H368" class="m-line" stroke="#f4b76b"/><text x="374" y="1">11 kV</text><path d="M414 -3.5H436" class="m-line" stroke="#4d5b69"/><text x="442" y="1">dead</text>
        <text x="0" y="18">Red filled: closed. Green hollow: open. Click a device to operate it.</text></g>
    </svg>`;
  }

  function preview(device, close) {
    const b = engine.byId[device], before = analysis(), res = engine.operate(sim.states, device, close, sim.fault);
    const minutes = b.control === 'field' ? scada.fieldMinutes : scada.remoteMinutes;
    if (res.blocked) return {blocked: true, lines: [{cls: 'm-over', text: `Interlocked: closing ${b.label} would connect two supplies in parallel.`}, {text: 'Open a switch on one side first, then close this one (break before make).'}]};
    const after = res.result, lines = [{text: `${b.control === 'field' ? 'Field crew operation' : 'SCADA remote command'} · about ${minutes} min`}];
    lines.push({text: `Customers off supply ${fmtInt(before.customersOff)} → ${fmtInt(after.customersOff)}`, cls: after.customersOff > before.customersOff ? 'm-over' : ''});
    for (const id of ['F1', 'F2', 'F3', 'F4', 'F5', 'F6', 'IC1', 'IC2']) {
      const a0 = before.flows[id] ? before.flows[id].amps : 0, a1 = after.flows[id] ? after.flows[id].amps : 0, limit = engine.byId[id].limitA;
      if (Math.abs(a1 - a0) > 0.5) lines.push({text: `${id} ${a0.toFixed(1)} → ${a1.toFixed(1)} A (${pct(a1, limit)}% of ${limit} A)`, cls: a1 > limit ? 'm-over' : a1 > 0.9 * limit ? 'm-warn' : ''});
    }
    for (const ev of res.events) {
      if (ev.type === 'trip') lines.push({cls: 'm-over', text: `${deviceLabel(ev.device)} would trip: this closes onto the fault on cable C1.`});
      if (ev.type === 'overload') lines.push({cls: 'm-over', text: `Overload: ${deviceLabel(ev.device)} at ${ev.amps.toFixed(1)} A, limit ${ev.limitA} A.`});
    }
    return {blocked: false, lines};
  }

  function renderCommand() {
    const box = $('#cr-command');
    if (!sim.selected) { box.innerHTML = `<p class="small muted">Select a breaker or switch on the diagram. Commands use select, preview, execute, like a real SCADA console.</p>`; return; }
    const id = sim.selected, b = engine.byId[id], closed = sim.states[id], A = analysis(), f = A.flows[id];
    const next = !closed;
    const pv = sim.command ? preview(id, sim.command.close) : null;
    box.innerHTML = `<div class="cr-cmd-head"><div><span class="eyebrow">SELECTED DEVICE</span><strong>${esc(b.label)}</strong></div><span class="cr-state ${closed ? 'closed' : 'open'}">${closed ? 'CLOSED' : 'OPEN'}</span></div>
      <p class="small muted">${b.control === 'field' ? 'Field operated: the control room instructs a crew on site.' : 'Remote: operated by SCADA from the control room.'}${f && f.amps > 0.05 ? ` Carrying ${f.amps.toFixed(1)} A.` : ''}${b.limitA ? ` Limit ${b.limitA} A.` : ''}</p>
      ${pv ? `<ul class="cr-preview">${pv.lines.map(l => `<li class="${l.cls || ''}">${esc(l.text)}</li>`).join('')}</ul>
        <div class="cr-cmd-actions">${pv.blocked ? '' : `<button class="primary" id="cr-exec">Execute ${sim.command.close ? 'close' : 'open'}</button>`}<button class="quiet" id="cr-cancel">Cancel</button></div>`
        : `<div class="cr-cmd-actions"><button class="cr-cmd" id="cr-prep">${next ? 'Close' : 'Open'} ${esc(id)}</button><span class="small muted">Preview the result before executing.</span></div>`}`;
    box.querySelector('#cr-prep')?.addEventListener('click', () => { sim.command = {device: id, close: next}; renderCommand(); });
    box.querySelector('#cr-exec')?.addEventListener('click', () => execute(id, sim.command.close));
    box.querySelector('#cr-cancel')?.addEventListener('click', () => { sim.command = null; renderCommand(); });
  }

  const drillSteps = () => [
    {text: 'Acknowledge the trip alarms and read the fault passage indicator.', done: () => !sim.events.some(e => e.sev === 'alarm' && !e.ack)},
    ...scada.drill.map(s => ({text: s.text, device: s.device, close: s.close, done: () => sim.states[s.device] === s.close}))
  ];

  function renderDrill(A) {
    const steps = drillSteps(), nextIndex = steps.findIndex(s => !s.done());
    const overloaded = Object.entries(A.flows).some(([id, f]) => engine.byId[id].limitA && f.amps > engine.byId[id].limitA);
    const complete = sim.drill && nextIndex === -1 && A.customersOff === 0 && !overloaded;
    $('#cr-drill').innerHTML = `<div class="panel-title"><h3>Switching schedule · cable fault on F2</h3><span class="pill">${sim.drill ? (complete ? 'Complete' : 'In progress') : 'Drill'}</span></div>
      <p class="small muted">At ${clockText(scada.faultTime)} an earth fault on cable C1 trips feeder F2 and takes ${fmtInt(scada.drillResult.customersAffected)} customers off supply. Follow the schedule, or operate the switches in your own order and compare the customer minutes.</p>
      <ol class="cr-steps">${steps.map((s, i) => `<li class="${!sim.drill ? '' : s.done() ? 'done' : i === nextIndex ? 'current' : ''}"><span class="mono">${s.done() && sim.drill ? '✓' : String(i + 1).padStart(2, '0')}</span><span>${esc(s.text)}${s.device ? ` <em>${engine.byId[s.device].control === 'field' ? 'field, 20 min' : 'SCADA, 1 min'}</em>` : ''}</span></li>`).join('')}</ol>
      ${complete ? `<div class="cr-result"><strong>All ${fmtInt(scada.drillResult.customersAffected)} customers restored at ${clockText(sim.clock)}.</strong><span>${fmtInt(sim.cmi)} customer minutes lost. The recommended order gives ${fmtInt(scada.drillResult.customerMinutes)}. Cable C1 is isolated and ready for the crew to earth, locate, repair and pressure test.</span></div>` : ''}
      <div class="cr-drill-actions">${!sim.drill ? '<button class="primary" id="cr-start">Start fault drill</button>' : nextIndex >= 0 ? '<button class="primary" id="cr-next">Do next step</button>' : ''}
        ${sim.fault && !A.energized.has('F2C') && !sim.states.RS1 && !sim.states.F2 ? '<button class="cr-cmd" id="cr-repair">Mark C1 repaired</button>' : ''}<button class="quiet" id="cr-reset">Reset to normal</button></div>`;
    $('#cr-start')?.addEventListener('click', startDrill);
    $('#cr-next')?.addEventListener('click', () => {
      const s = drillSteps()[nextIndex];
      if (!s.device) { acknowledge(); return; }
      select(s.device, true);
      execute(s.device, s.close);
    });
    $('#cr-repair')?.addEventListener('click', () => { sim.fault = null; sim.drill = false; log('info', 'C1', 'Cable C1 repaired, jointed and pressure tested. Restore normal feeding break before make.'); update(); });
    $('#cr-reset')?.addEventListener('click', reset);
  }

  function renderEvents() {
    $('#cr-events').innerHTML = sim.events.length ? sim.events.map(e => `<li class="${e.sev}${e.ack ? '' : ' unack'}"><span class="mono">${e.time}</span><span class="mono cr-dev">${esc(e.dev)}</span><span>${esc(e.text)}</span></li>`).join('')
      : `<li class="info"><span class="mono">${clockText(sim.clock)}</span><span></span><span>Network in normal configuration. No events.</span></li>`;
  }

  function renderInfo() {
    const box = $('#cr-info');
    if (!sim.picked) { box.hidden = true; return; }
    const a = assets[sim.picked] || EXTRA_ASSETS[sim.picked];
    if (!a) { box.hidden = true; return; }
    const A = analysis(), on = n => A.energized.has(n), st = id => sim.states[id] ? 'closed' : 'open';
    const live = {
      abs: `ABS ${st('ABS')} · tie cable ${on('TIE') ? 'live' : 'dead'}`,
      rmu: `RS-1 ${st('RS1')} · RS-2 ${st('RS2')} · RS-3 ${st('RS3')} · tee ${st('TF1')}`,
      switchgear: `F1 ${(A.flows.F1?.amps || 0).toFixed(0)} A · F2 ${(A.flows.F2?.amps || 0).toFixed(0)} A · BC ${st('BC')}`,
      powertx: `T1 ${((A.flows.T1?.mw || 0) / scada.pf).toFixed(1)} MVA · T2 ${((A.flows.T2?.mw || 0) / scada.pf).toFixed(1)} MVA`,
      commercial: `Supply ${on('CSS') ? 'on' : 'off'} · 420 customers`,
      kiosk: `Supply ${on('CSS') ? 'on' : 'off'} · 0.38 MW`,
      community: `Supply ${on('F1L') ? 'on' : 'off'} · PMT-1 and PMT-2`,
      pmt: `Supply ${on('F1L') ? 'on' : 'off'}`,
      overhead: `F1 ${on('F1L') ? 'live' : 'dead'} · ${(A.flows.F1?.amps || 0).toFixed(1)} A`,
      ring: `Supply ${on('C2') ? 'on' : 'off'} · fed ${A.parent.C2 ? (A.parent.C2.branch === 'NO6' ? 'from F4' : 'from F2 ring') : 'from nowhere'}`,
      cable: `Cable C1 ${sim.fault ? 'faulted' : on('F2C') ? 'live' : 'dead'}`,
      fault: sim.fault ? 'Cable C1 faulted and isolated for repair' : 'No fault',
      feeders: `F3 to F6 ${['F3', 'F4', 'F5', 'F6'].filter(id => sim.states[id]).length} of 4 closed`
    }[sim.picked] || '';
    box.hidden = false;
    box.innerHTML = `<button class="quiet cr-info-close" aria-label="Close">✕</button><span class="eyebrow">${esc(a.tag)}</span><strong>${esc(a.title)}</strong><span class="mono">${esc(a.rating)}</span>${live ? `<span class="cr-live-state">${esc(live)}</span>` : ''}`;
    box.querySelector('.cr-info-close').addEventListener('click', () => { sim.picked = null; twin?.select(null); renderInfo(); });
  }

  function update() {
    const A = analysis();
    renderHmi(A); renderMimic(A); renderCommand(); renderDrill(A); renderEvents(); renderInfo();
    twin?.setState(snapshot(A));
  }

  function select(device, fly) {
    sim.selected = device; sim.command = null;
    if (sim.follow && fly !== false) twin?.focus(device);
    update();
  }

  function execute(device, close) {
    const b = engine.byId[device], before = analysis(), res = engine.operate(sim.states, device, close, sim.fault);
    sim.command = null;
    if (res.blocked) { log('warn', device, `Interlock: closing ${b.label} would connect two supplies in parallel. Open a switch first.`); update(); return; }
    const minutes = b.control === 'field' ? scada.fieldMinutes : scada.remoteMinutes;
    sim.cmi += before.customersOff * minutes; sim.clock += minutes;
    sim.states = res.states;
    log('cmd', device, `${b.label} ${close ? 'closed' : 'opened'} ${b.control === 'field' ? 'by the field crew' : 'by SCADA'}`);
    for (const ev of res.events) {
      if (ev.type === 'trip') log('alarm', ev.device, `${deviceLabel(ev.device)} tripped: switched onto the fault on cable C1`);
      if (ev.type === 'overload') log('alarm', ev.device, `Overload on ${deviceLabel(ev.device)}: ${ev.amps.toFixed(1)} A, limit ${ev.limitA} A`);
    }
    const after = analysis(), delta = before.customersOff - after.customersOff;
    if (delta > 0) log('info', device, `${fmtInt(delta)} customers restored`);
    if (delta < 0) log('alarm', device, `${fmtInt(-delta)} customers lost supply`);
    const overloads = Object.entries(after.flows).filter(([id, f]) => engine.byId[id].limitA && f.amps > engine.byId[id].limitA);
    if (sim.drill && before.customersOff > 0 && after.customersOff === 0) {
      if (overloads.length) log('warn', 'GS-1', `All customers are on supply, but ${overloads.map(([id, f]) => `${id} carries ${f.amps.toFixed(1)} A against ${engine.byId[id].limitA} A`).join(' and ')}. Split the load before the conductor overheats.`);
      else log('info', 'GS-1', `All customers restored within limits. ${fmtInt(sim.cmi)} customer minutes lost.`);
    }
    update();
  }

  function acknowledge() { sim.events.forEach(e => { e.ack = true; }); update(); }

  function startDrill() {
    sim.states = engine.normal(); sim.fault = scada.faultNode; sim.clock = scada.faultTime; sim.cmi = 0; sim.events = []; sim.drill = true; sim.selected = null; sim.command = null;
    const tripped = engine.protect(sim.states, sim.fault);
    sim.states = tripped.states;
    const A = analysis();
    log('alarm', 'F2', 'Feeder F2 breaker tripped: earth fault protection, phase B');
    log('alarm', 'F2', `Feeder F2 dead: ${fmtInt(A.customersOff)} customers off supply`);
    log('info', 'RMU-1', 'Fault passage indicator on RS-1 did not operate: the fault is on cable C1, between GS-1 and RMU-1');
    twin?.view('underground');
    update();
  }

  function reset() {
    sim.states = engine.normal(); sim.fault = null; sim.clock = startClock; sim.cmi = 0; sim.events = []; sim.drill = false; sim.selected = null; sim.command = null;
    log('info', 'GS-1', 'Network restored to its normal configuration');
    update();
  }

  // Wiring.
  $('#cr-mimic').addEventListener('click', e => { const g = e.target.closest('[data-dev]'); if (g) select(g.dataset.dev); });
  $('#cr-mimic').addEventListener('keydown', e => { const g = e.target.closest('[data-dev]'); if (g && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); select(g.dataset.dev); root.querySelector(`[data-dev="${g.dataset.dev}"]`)?.focus(); } });
  $('#cr-ack').addEventListener('click', acknowledge);
  $('#cr-follow').addEventListener('change', e => { sim.follow = e.target.checked; });
  root.querySelectorAll('[data-view3d]').forEach(b => b.addEventListener('click', () => twin?.view(b.dataset.view3d)));
  const toggle = (id, fn) => $(id).addEventListener('click', e => { const on = e.currentTarget.getAttribute('aria-pressed') !== 'true'; e.currentTarget.setAttribute('aria-pressed', String(on)); fn(on); });
  toggle('#cr-xray', on => twin?.setXray(on));
  toggle('#cr-flow', on => twin?.setFlow(on));
  toggle('#cr-labels', on => twin?.setLabels(on));
  $('#cr-zoomin').addEventListener('click', () => twin?.zoom(0.8));
  $('#cr-zoomout').addEventListener('click', () => twin?.zoom(1.25));
  log('info', 'GS-1', 'Network in normal configuration');
  update();
  return {resume: () => twin?.resume(), pause: () => twin?.pause(), check};
}
