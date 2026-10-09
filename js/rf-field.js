/* Live RF background: a 2D Maxwell FDTD (Yee grid) solve behind the page.
   - TMz polarization: Ez, Hx, Hy  (E perpendicular to the screen)
   - TEz polarization: Hz, Ex, Ey  (E in the plane of the screen)
   - Circular: both run together, driven 90 degrees apart
   A TX antenna radiates; the cursor is a perfectly conducting disc, so its scattered field
   interferes with the direct wave at the RX antenna. The RX signal is FFT'd into the hero
   spectrum panel, which also reads out received amplitude, phase (I/Q against the TX) and the
   bistatic Doppler shift of the moving reflector. */
(function () {
  var canvas = document.getElementById('bg');
  if (!canvas) return;
  var ctx = canvas.getContext('2d');
  // a second, transparent canvas at device resolution for crisp vector overlays (strokes, cursor)
  var ink2 = document.createElement('canvas');
  ink2.id = 'bg-ink'; ink2.setAttribute('aria-hidden', 'true');
  canvas.parentNode.insertBefore(ink2, canvas.nextSibling);
  var ink2ctx = ink2.getContext('2d'), octx = ctx, sep = false;
  var reduce = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  var CELL = 7;                 // css px per Yee cell
  var S = 0.5;                  // Courant number c·dt/dx (2D limit is 1/sqrt 2)
  var STEPS = reduce ? 1 : 3;   // solver steps per frame (adapts to the machine below)
  var MAX_STEPS = STEPS, solveMs = 0;
  var SPONGE = 30;              // graded absorbing border (cells)
  var F0 = 1 / 36;              // carrier, cycles per step  ->  lambda = S/F0 = 18 cells
  var N = 1024;                 // RX record length for the FFT
  var ARROW = 6;                // cells between in-plane field arrows

  var MODES = ['CW', 'FMCW', 'PULSE'];
  var POLS = { tm: 'TMz · E ⊥ screen', te: 'TEz · E in plane', circ: 'Circular · TM + TE at 90°' };
  var state = { pol: 'tm', view: 'E', mode: 2 };

  var W, H, n, damp, wall, img, off, offCtx;
  var Ez, Hx, Hy, Hz, Ex, Ey;
  var tx = {}, rx = {}, posts = [];
  var refl = { x: 0, y: 0, r: 4.5, on: false };
  // Drawn material, per cell: remaining life, brush weight, age, material, decay rate and stroke id
  var ink, inkW, inkAge, inkMat, inkDecay, inkStroke, inkList = [], drawing = null;
  var soft, softList = [];   // conductor strength 0..1 (cursor disc + metal ink)
  var loss, lossList = [];   // absorber strength 0..1
  var ce, glassList = [];    // E-update coefficient 1/eps_r (glass ink)
  var MAT = { metal: 0, absorb: 1, glass: 2 };
  var MAT_RGB = [[225, 235, 255], [240, 173, 78], [74, 222, 128]];
  var EPS_GLASS = 4;          // relative permittivity of the glass brush (n = 2)
  var FADE_S = 2.5;           // seconds a stroke takes to fade once its lifetime is up
  var brush = { size: 2.6, life: 3, mat: 0, tool: 'free', sym: 'none' };
  var strokeId = 0, strokeStack = [], sources = [], preview = null;
  var vstrokes = [], dpr = 1;   // vector copy of every stroke, drawn at screen resolution
  var mouse = { x: -1, y: -1 };
  var step = 0, phase = 0, gain = 30;
  var rxBuf = new Float32Array(N), txBuf = new Float32Array(N), bi = 0;

  function setup() {
    var vw = window.innerWidth, vh = window.innerHeight;
    canvas.width = vw; canvas.height = vh;
    dpr = Math.min(window.devicePixelRatio || 1, 2);
    // high-DPI screens get the separate device-resolution layer; at 1x the main canvas is already sharp
    sep = dpr > 1;
    ink2.style.display = sep ? '' : 'none';
    octx = sep ? ink2ctx : ctx;
    ink2.width = sep ? Math.round(vw * dpr) : 1; ink2.height = sep ? Math.round(vh * dpr) : 1;
    lastBox = null;
    W = Math.ceil(vw / CELL) + 2; H = Math.ceil(vh / CELL) + 2; n = W * H;
    Ez = new Float32Array(n); Hx = new Float32Array(n); Hy = new Float32Array(n);
    Hz = new Float32Array(n); Ex = new Float32Array(n); Ey = new Float32Array(n);
    damp = new Float32Array(n); wall = new Uint8Array(n); ink = new Float32Array(n); inkW = new Float32Array(n); inkAge = new Uint8Array(n); inkList = [];
    inkMat = new Uint8Array(n); inkDecay = new Float32Array(n); inkStroke = new Int32Array(n);
    soft = new Float32Array(n); softList = []; loss = new Float32Array(n); lossList = [];
    ce = new Float32Array(n).fill(1); glassList = []; sources = [];
    for (var y = 0; y < H; y++) for (var x = 0; x < W; x++) {
      var d = Math.min(x, y, W - 1 - x, H - 1 - y);
      damp[y * W + x] = d < SPONGE ? 1 - 0.06 * Math.pow((SPONGE - d) / SPONGE, 3) : 1;
    }
    var wide = vw > 900;
    tx = { x: Math.round(W * 0.80), y: Math.round(H * (wide ? 0.30 : 0.36)) };
    rx = { x: tx.x + (wide ? 6 : -6), y: tx.y + 7 };
    posts = (wide ? [[0.93, 0.62], [0.64, 0.80], [0.96, 0.14]] : [[0.18, 0.92], [0.86, 0.66]])
      .map(function (p) { return { x: Math.round(W * p[0]), y: Math.round(H * p[1]), r: 2.4 }; });
    posts.forEach(function (p) { stamp(p, 1); });
    off = document.createElement('canvas'); off.width = W; off.height = H;
    offCtx = off.getContext('2d');
    img = offCtx.createImageData(W, H);
  }

  function stamp(o, v) {
    var r = Math.ceil(o.r) + 1, cx = Math.round(o.x), cy = Math.round(o.y);
    for (var y = -r; y <= r; y++) for (var x = -r; x <= r; x++) {
      var X = cx + x, Y = cy + y;
      if (X > 1 && Y > 1 && X < W - 2 && Y < H - 2 && x * x + y * y <= o.r * o.r) {
        var i = Y * W + X;
        if (v) { wall[i] = 1; Ez[i] = Ex[i] = Ey[i] = 0; } else wall[i] = 0;
      }
    }
  }

  function txSample(offset) {
    var a = 1;
    if (state.mode === 2) { var k = step % 420; a = Math.exp(-Math.pow((k - 40) / 14, 2)); } // gaussian pulses
    return a * Math.sin(phase + offset);
  }

  function moveReflector() {
    if (!refl.on) return;
    var tx_ = mouse.x / CELL, ty_ = mouse.y / CELL;
    refl.x = tx_; refl.y = ty_;   // the reflector sits exactly under the cursor
  }

  function stepTM(src) {
    var x, y, i;
    for (y = 0; y < H - 1; y++) for (x = 0; x < W - 1; x++) {
      i = y * W + x;
      Hx[i] = (Hx[i] - S * (Ez[i + W] - Ez[i])) * damp[i];
      Hy[i] = (Hy[i] + S * (Ez[i + 1] - Ez[i])) * damp[i];
    }
    for (y = 1; y < H - 1; y++) for (x = 1; x < W - 1; x++) {
      i = y * W + x;
      if (wall[i]) { Ez[i] = 0; continue; }   // PEC: tangential E vanishes
      Ez[i] = (Ez[i] + S * ce[i] * ((Hy[i] - Hy[i - 1]) - (Hx[i] - Hx[i - W]))) * damp[i];
    }
    var t = tx.y * W + tx.x;
    Ez[t] += src; Ez[t + 1] += src * 0.5; Ez[t - 1] += src * 0.5;
    for (var k = 0; k < sources.length; k++) Ez[sources[k].i] += src * Math.min(1, sources[k].life);
  }

  function stepTE(src) {
    var x, y, i;
    for (y = 1; y < H - 1; y++) for (x = 1; x < W - 1; x++) {
      i = y * W + x;
      if (wall[i]) { Ex[i] = Ey[i] = 0; continue; }   // PEC: in-plane E vanishes
      Ex[i] = (Ex[i] + S * ce[i] * (Hz[i] - Hz[i - W])) * damp[i];
      Ey[i] = (Ey[i] - S * ce[i] * (Hz[i] - Hz[i - 1])) * damp[i];
    }
    for (y = 0; y < H - 1; y++) for (x = 0; x < W - 1; x++) {
      i = y * W + x;
      Hz[i] = (Hz[i] - S * ((Ey[i + 1] - Ey[i]) - (Ex[i + W] - Ex[i]))) * damp[i];
    }
    var t = tx.y * W + tx.x;
    Hz[t] += src; Hz[t + 1] += src * 0.5; Hz[t - 1] += src * 0.5;
    for (var k = 0; k < sources.length; k++) Hz[sources[k].i] += src * Math.min(1, sources[k].life);
  }

  // The cursor disc and drawn walls are soft-edged conductors: each cell has a strength s in
  // 0..1 and E is scaled by (1 - s) after every update — s = 1 is a perfect conductor, smaller s a
  // lossy, partly reflecting sheet. Tapering s over ~1.5 cells at the edges keeps a moving or
  // fading boundary from exciting grid-scale (checkerboard) noise the way a hard edge does.
  function buildSoft() {
    var k, i;
    for (k = 0; k < softList.length; k++) soft[softList[k]] = 0;
    for (k = 0; k < lossList.length; k++) loss[lossList[k]] = 0;
    for (k = 0; k < glassList.length; k++) ce[glassList[k]] = 1;
    softList = []; lossList = []; glassList = [];
    function put(i, s) {
      if (s <= 0) return;
      if (soft[i] === 0) softList.push(i);
      if (s > soft[i]) soft[i] = s;
    }
    if (refl.on) {
      var R = refl.r + 2, cx = refl.x, cy = refl.y;
      for (var y = Math.floor(cy - R); y <= Math.ceil(cy + R); y++) for (var x = Math.floor(cx - R); x <= Math.ceil(cx + R); x++) {
        if (x < 2 || y < 2 || x > W - 3 || y > H - 3) continue;
        var d = Math.hypot(x - cx, y - cy);
        put(y * W + x, Math.max(0, Math.min(1, (refl.r + 1 - d) / 2)));
      }
    }
    // drawn material: full strength for its lifetime, then fades; new strokes ramp in over a few frames
    var live = [];
    for (k = 0; k < inkList.length; k++) {
      i = inkList[k];
      ink[i] -= inkDecay[i];
      if (inkAge[i] < 255) inkAge[i]++;
      if (ink[i] <= 0) { ink[i] = 0; inkW[i] = 0; continue; }
      live.push(i);
      var s = inkW[i] * Math.min(1, ink[i]) * Math.min(1, inkAge[i] / 12);
      if (inkMat[i] === MAT.metal) put(i, s);
      else if (inkMat[i] === MAT.absorb) { if (loss[i] === 0) lossList.push(i); loss[i] = Math.max(loss[i], s); }
      else { ce[i] = 1 / (1 + (EPS_GLASS - 1) * s); glassList.push(i); }
    }
    inkList = live;
    var vs = [];
    for (k = 0; k < vstrokes.length; k++) {
      var st = vstrokes[k]; st.life -= st.decay; st.age++;
      if (st.life > 0) vs.push(st);
    }
    vstrokes = vs;
    var ls = [];
    for (k = 0; k < sources.length; k++) { sources[k].life -= sources[k].decay; if (sources[k].life > 0) ls.push(sources[k]); }
    sources = ls;
  }

  function applySoft(tm, te) {
    var k, i, keep;
    for (k = 0; k < softList.length; k++) {
      i = softList[k]; keep = 1 - soft[i];
      if (tm) Ez[i] *= keep;
      if (te) { Ex[i] *= keep; Ey[i] *= keep; }
    }
    // absorber: a strong but gradual loss each step, so waves die inside instead of bouncing off
    for (k = 0; k < lossList.length; k++) {
      i = lossList[k]; keep = 1 - 0.18 * loss[i];
      if (tm) Ez[i] *= keep;
      if (te) { Ex[i] *= keep; Ey[i] *= keep; }
    }
  }

  function lifeParams() {
    // full strength for brush.life seconds, then FADE_S seconds of fading (decay is per frame)
    if (!isFinite(brush.life)) return [1, 0];
    return [1 + brush.life / FADE_S, 1 / (FADE_S * 60)];
  }

  function vstroke(id) {
    var s = vstrokes[vstrokes.length - 1];
    if (s && s.id === id) return s;
    var lp = lifeParams();
    s = { id: id, mat: brush.mat, w: brush.size * CELL * 1.7, segs: [], life: lp[0], decay: lp[1], age: 0,
          box: [Infinity, Infinity, -Infinity, -Infinity] };
    vstrokes.push(s);
    return s;
  }

  // smooth, full-resolution rendering of the drawn material (the solver itself works on the grid)
  function drawStrokes(fade) {
    octx.lineCap = 'round'; octx.lineJoin = 'round';
    for (var k = 0; k < vstrokes.length; k++) {
      var s = vstrokes[k], c = MAT_RGB[s.mat], a = Math.min(1, s.life) * Math.min(1, s.age / 12) * fade;
      if (a <= 0.01) continue;
      octx.beginPath();
      for (var j = 0; j < s.segs.length; j++) {
        var g = s.segs[j];
        if (j === 0 || g[0] !== s.segs[j - 1][2] || g[1] !== s.segs[j - 1][3]) octx.moveTo(g[0], g[1]);
        octx.lineTo(g[2], g[3]);
      }
      var rgb = 'rgb(' + c.join(',') + ')';
      // soft halo, translucent body, bright thin core
      octx.strokeStyle = rgb; octx.globalAlpha = 0.10 * a; octx.lineWidth = s.w + 8; octx.stroke();
      octx.globalAlpha = (s.mat === MAT.glass ? 0.22 : 0.38) * a; octx.lineWidth = s.w; octx.stroke();
      octx.globalAlpha = (s.mat === MAT.glass ? 0.5 : 0.85) * a; octx.lineWidth = Math.max(1, s.w * 0.18); octx.stroke();
    }
    octx.globalAlpha = 1; octx.lineWidth = 1.2;
  }

  function paintRaw(ax, ay, bx, by, id) {
    var vs_ = vstroke(id), bx_ = vs_.box;
    vs_.segs.push([ax, ay, bx, by]);
    bx_[0] = Math.min(bx_[0], ax, bx); bx_[1] = Math.min(bx_[1], ay, by);
    bx_[2] = Math.max(bx_[2], ax, bx); bx_[3] = Math.max(bx_[3], ay, by);
    var x0 = ax / CELL, y0 = ay / CELL, x1 = bx / CELL, y1 = by / CELL, lp = lifeParams();
    var len = Math.hypot(x1 - x0, y1 - y0), R = brush.size, steps = Math.max(1, Math.ceil(len * 2));
    var taper = Math.min(1.8, Math.max(0.8, R * 0.6));
    for (var s = 0; s <= steps; s++) {
      var cx = x0 + ((x1 - x0) * s) / steps, cy = y0 + ((y1 - y0) * s) / steps;
      for (var y = Math.floor(cy - R); y <= Math.ceil(cy + R); y++) for (var x = Math.floor(cx - R); x <= Math.ceil(cx + R); x++) {
        if (x < 2 || y < 2 || x > W - 3 || y > H - 3) continue;
        var w = Math.min(1, (R - Math.hypot(x - cx, y - cy)) / taper);   // solid core, tapered edge
        if (w <= 0) continue;
        var i = y * W + x;
        if (ink[i] <= 0 || inkMat[i] !== brush.mat) { if (ink[i] <= 0) inkList.push(i); inkAge[i] = 0; inkW[i] = 0; }
        ink[i] = lp[0]; inkDecay[i] = lp[1]; inkMat[i] = brush.mat; inkStroke[i] = id;
        if (w > inkW[i]) inkW[i] = w;
      }
    }
  }

  // symmetry copies about the centre of the viewport
  function symmetric(pt) {
    var cx = window.innerWidth / 2, cy = window.innerHeight / 2, x = pt[0] - cx, y = pt[1] - cy, out = [];
    if (brush.sym === 'mirror') out = [[x, y], [-x, y]];
    else if (brush.sym === 'quad') out = [[x, y], [-x, y], [x, -y], [-x, -y]];
    else if (brush.sym === 'radial') for (var k = 0; k < 6; k++) {
      var a = (k * Math.PI) / 3; out.push([x * Math.cos(a) - y * Math.sin(a), x * Math.sin(a) + y * Math.cos(a)]);
    }
    else out = [[x, y]];
    return out.map(function (q) { return [q[0] + cx, q[1] + cy]; });
  }

  function paintPath(pts, id) {
    for (var k = 0; k < pts.length - 1 || k === 0; k++) {
      var A = symmetric(pts[k]), B = symmetric(pts[Math.min(k + 1, pts.length - 1)]);
      for (var j = 0; j < A.length; j++) paintRaw(A[j][0], A[j][1], B[j][0], B[j][1], id);
      if (pts.length === 1) break;
    }
  }

  function addSource(pt, id) {
    var lp = lifeParams();
    symmetric(pt).forEach(function (q) {
      var x = Math.round(q[0] / CELL), y = Math.round(q[1] / CELL);
      if (x < 3 || y < 3 || x > W - 4 || y > H - 4) return;
      sources.push({ i: y * W + x, x: x, y: y, life: lp[0], decay: lp[1], stroke: id });
    });
  }

  // outline of a shape tool between press point a and current point b (page px)
  function shapePoints(tool, a, b) {
    var dx = b[0] - a[0], dy = b[1] - a[1], L = Math.hypot(dx, dy), pts = [], k;
    if (tool === 'line') return [a, b];
    if (tool === 'ring') {
      for (k = 0; k <= 72; k++) { var t = (k / 72) * 2 * Math.PI; pts.push([a[0] + L * Math.cos(t), a[1] + L * Math.sin(t)]); }
      return pts;
    }
    if (tool === 'dish') {
      // parabolic reflector: a = focus, b = vertex, focal length f = |ab|; rim level with the focus
      var f = Math.max(L, 8), ux = (a[0] - b[0]) / (L || 1), uy = (a[1] - b[1]) / (L || 1), vx = -uy, vy = ux;
      for (k = -40; k <= 40; k++) {
        var s = (k / 40) * 2 * f, along = (s * s) / (4 * f);
        pts.push([b[0] + vx * s + ux * along, b[1] + vy * s + uy * along]);
      }
      return pts;
    }
    return [a];
  }

  function commitShape(tool, a, b) {
    var id = ++strokeId;
    strokeStack.push(id);
    if (tool === 'antenna') { addSource(a, id); return; }
    paintPath(shapePoints(tool, a, b), id);
    if (tool === 'dish') addSource(a, id);   // a feed at the focus: the dish turns it into a plane wave
  }

  function undo() {
    var id = strokeStack.pop();
    if (id === undefined) return;
    for (var k = 0; k < inkList.length; k++) if (inkStroke[inkList[k]] === id) ink[inkList[k]] = 0;
    sources = sources.filter(function (s) { return s.stroke !== id; });
    vstrokes = vstrokes.filter(function (s) { return s.id !== id; });
  }

  function clearAll() {
    for (var k = 0; k < inkList.length; k++) ink[inkList[k]] = 0;
    sources = []; strokeStack = []; vstrokes = [];
  }

  function solve() {
    moveReflector();
    buildSoft();
    var tm = state.pol !== 'te', te = state.pol !== 'tm';
    for (var s = 0; s < STEPS; s++) {
      var f = state.mode === 1 ? F0 * (0.75 + 0.5 * ((step % 900) / 900)) : F0;   // FMCW: sawtooth chirp
      phase += 2 * Math.PI * f;
      var a = txSample(0), b = txSample(Math.PI / 2);
      if (tm) stepTM(a * 0.5);
      if (te) stepTE((state.pol === 'circ' ? b : a) * 0.5);
      applySoft(tm, te);
      var r = rx.y * W + rx.x;
      // RX antenna: co-polar E (Ez for TM, Ey for TE)
      rxBuf[bi] = (tm ? Ez[r] : 0) + (te ? Ey[r] * 2 : 0);
      txBuf[bi] = a;
      bi = (bi + 1) % N;
      step++;
    }
  }

  // colour = signed out-of-plane component; arrows = in-plane vector, for the chosen view
  function fields() {
    var tm = state.pol !== 'te', te = state.pol !== 'tm';
    if (state.view === 'E') return { scalar: tm ? Ez : null, vx: te ? Ex : null, vy: te ? Ey : null };
    return { scalar: te ? Hz : null, vx: tm ? Hx : null, vy: tm ? Hy : null };
  }

  function draw(fade) {
    var F = fields(), d = img.data, ss = 0, cnt = 0, i, p, v, m;
    var sc = F.scalar, vx = F.vx, vy = F.vy;
    for (i = 0; i < n; i += 7) {
      v = sc ? sc[i] : Math.hypot(vx[i], vy[i]);
      ss += v * v; cnt++;
    }
    var rms = Math.sqrt(ss / cnt);
    gain += ((rms > 1e-7 ? 0.55 / rms : 30) - gain) * 0.03;
    gain = Math.max(1, Math.min(400, gain));
    for (i = 0, p = 0; i < n; i++, p += 4) {
      if (wall[i]) { d[p] = 210; d[p + 1] = 225; d[p + 2] = 255; d[p + 3] = 80 * fade; continue; }
      if (sc) {
        v = sc[i];
        m = Math.tanh(Math.abs(v) * gain);
        if (v > 0) { d[p] = 0; d[p + 1] = 229; d[p + 2] = 255; } else { d[p] = 124; d[p + 1] = 77; d[p + 2] = 255; }
      } else {
        // only an in-plane field in this view: shade by its magnitude
        m = Math.tanh(Math.hypot(vx[i], vy[i]) * gain);
        d[p] = 40 + 120 * m; d[p + 1] = 140 + 80 * m; d[p + 2] = 255;
      }
      d[p + 3] = m * 62 * fade;
    }
    offCtx.putImageData(img, 0, 0);
    ctx.fillStyle = '#080a0f';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.imageSmoothingEnabled = true;
    ctx.drawImage(off, 0, 0, W * CELL, H * CELL);

    if (vx) {   // in-plane vector field as short arrows
      var ag = gain * (sc ? 1.4 : 1);
      ctx.strokeStyle = state.view === 'E' ? '#00e5ff' : '#f0abfc';
      ctx.lineWidth = 1;
      ctx.globalAlpha = 0.55 * fade;
      ctx.beginPath();
      for (var y = ARROW / 2; y < H - 1; y += ARROW) for (var x = ARROW / 2; x < W - 1; x += ARROW) {
        i = y * W + x;
        var ax = vx[i], ay = vy[i], mg = Math.hypot(ax, ay);
        if (mg * ag < 0.08 || wall[i]) continue;
        var L = (Math.tanh(mg * ag) * CELL * ARROW * 0.42) / mg;
        var X = x * CELL + CELL / 2, Y = y * CELL + CELL / 2, ex = ax * L, ey = ay * L;
        var ux = ex / (Math.hypot(ex, ey) || 1), uy = ey / (Math.hypot(ex, ey) || 1), hx = X + ex, hy = Y + ey;
        ctx.moveTo(X - ex, Y - ey); ctx.lineTo(hx, hy);
        ctx.moveTo(hx, hy); ctx.lineTo(hx - 4 * ux + 2.5 * uy, hy - 4 * uy - 2.5 * ux);
        ctx.moveTo(hx, hy); ctx.lineTo(hx - 4 * ux - 2.5 * uy, hy - 4 * uy + 2.5 * ux);
      }
      ctx.stroke();
    }

    ctx.font = '10px "CMU Typewriter Text", monospace';
    ctx.lineWidth = 1.2;
    [[tx, 'TX', '#00e5ff'], [rx, 'RX', '#a78bfa']].forEach(function (a) {
      var X = a[0].x * CELL + CELL / 2, Y = a[0].y * CELL + CELL / 2;
      ctx.strokeStyle = a[2]; ctx.globalAlpha = 0.85 * fade;
      ctx.beginPath(); ctx.moveTo(X - 6, Y - 9); ctx.lineTo(X, Y); ctx.lineTo(X + 6, Y - 9); ctx.moveTo(X, Y); ctx.lineTo(X, Y + 9); ctx.stroke();
      ctx.fillStyle = a[2]; ctx.fillText(a[1], X + 9, Y + 4);
    });
    ctx.globalAlpha = 1;
  }

  // crisp overlay at device resolution: drawn material, antennas, shape preview, cursor ring
  // Only the region that changed is cleared each frame: the union of this frame's and last frame's
  // bounding boxes, so a cursor ring alone costs a few hundred pixels instead of the whole screen.
  var lastBox = null;
  function overlayBox() {
    var b = [Infinity, Infinity, -Infinity, -Infinity], k;
    function add(x0, y0, x1, y1, pad) {
      b[0] = Math.min(b[0], x0 - pad); b[1] = Math.min(b[1], y0 - pad);
      b[2] = Math.max(b[2], x1 + pad); b[3] = Math.max(b[3], y1 + pad);
    }
    for (k = 0; k < vstrokes.length; k++) { var s = vstrokes[k]; add(s.box[0], s.box[1], s.box[2], s.box[3], s.w / 2 + 8); }
    for (k = 0; k < sources.length; k++) { var X = sources[k].x * CELL, Y = sources[k].y * CELL; add(X, Y, X, Y, 14); }
    if (preview) shapePoints(preview.tool, preview.a, preview.b).forEach(function (q) {
      symmetric(q).forEach(function (r) { add(r[0], r[1], r[0], r[1], brush.size * CELL + 8); });
    });
    if (refl.on) { var rx_ = refl.x * CELL, ry_ = refl.y * CELL, rr = refl.r * CELL; add(rx_, ry_, rx_, ry_, rr + 4); }
    return b[0] === Infinity ? null : b;
  }
  function drawOverlay(fade) {
    if (!sep) { octx.setTransform(1, 0, 0, 1, 0, 0); paintOverlay(fade); return; }
    var box = overlayBox();
    if (!box && !lastBox) return;
    var c = lastBox && box ? [Math.min(box[0], lastBox[0]), Math.min(box[1], lastBox[1]), Math.max(box[2], lastBox[2]), Math.max(box[3], lastBox[3])] : (box || lastBox);
    octx.setTransform(1, 0, 0, 1, 0, 0);
    octx.clearRect(Math.floor(c[0] * dpr) - 2, Math.floor(c[1] * dpr) - 2, Math.ceil((c[2] - c[0]) * dpr) + 4, Math.ceil((c[3] - c[1]) * dpr) + 4);
    lastBox = box;
    if (!box) return;
    octx.setTransform(dpr, 0, 0, dpr, 0, 0);
    paintOverlay(fade);
  }

  function paintOverlay(fade) {
    drawStrokes(fade);
    octx.lineWidth = 1.2;
    sources.forEach(function (s) {
      var X = s.x * CELL + CELL / 2, Y = s.y * CELL + CELL / 2;
      octx.strokeStyle = '#facc15'; octx.globalAlpha = 0.85 * fade * Math.min(1, s.life);
      octx.beginPath(); octx.moveTo(X - 5, Y - 8); octx.lineTo(X, Y); octx.lineTo(X + 5, Y - 8); octx.moveTo(X, Y); octx.lineTo(X, Y + 8); octx.stroke();
    });
    if (preview) {
      var col = MAT_RGB[brush.mat];
      octx.strokeStyle = preview.tool === 'antenna' ? '#facc15' : 'rgb(' + col.join(',') + ')';
      octx.globalAlpha = 0.8; octx.lineWidth = Math.max(1, brush.size * CELL * 0.6); octx.setLineDash([6, 6]);
      var pts = shapePoints(preview.tool, preview.a, preview.b);
      pts[0] && symmetric(pts[0]).forEach(function (_, j) {
        octx.beginPath();
        pts.forEach(function (q, k) { var r = symmetric(q)[j]; if (k) octx.lineTo(r[0], r[1]); else octx.moveTo(r[0], r[1]); });
        octx.stroke();
      });
      octx.setLineDash([]); octx.lineWidth = 1.2;
    }
    if (refl.on) {
      octx.globalAlpha = 0.9 * fade;
      octx.strokeStyle = '#e2e8f0';
      octx.beginPath(); octx.arc(refl.x * CELL, refl.y * CELL, refl.r * CELL, 0, Math.PI * 2); octx.stroke();
    }
    octx.globalAlpha = 1;
  }

  /* ── spectrum panel ── */
  var panel = document.getElementById('rf-spectrum');
  var sc2, sctx, read = {};
  if (panel) {
    sc2 = panel.querySelector('canvas'); sctx = sc2.getContext('2d');
    ['amp', 'ph', 'dop', 'mode', 'pol'].forEach(function (k) { read[k] = panel.querySelector('[data-r="' + k + '"]'); });
    panel.querySelector('[data-act="wave"]').onclick = function () {
      state.mode = (state.mode + 1) % MODES.length;
      this.textContent = 'waveform: ' + MODES[state.mode];
    };
    panel.querySelectorAll('[data-view]').forEach(function (b) {
      b.onclick = function () {
        state.view = b.dataset.view;
        panel.querySelectorAll('[data-view]').forEach(function (o) { o.classList.toggle('on', o === b); });
      };
    });
    panel.querySelectorAll('[data-pol]').forEach(function (b) {
      b.onclick = function () {
        state.pol = b.dataset.pol;
        panel.querySelectorAll('[data-pol]').forEach(function (o) { o.classList.toggle('on', o === b); });
        if (read.pol) read.pol.textContent = POLS[state.pol];
        Ez.fill(0); Hx.fill(0); Hy.fill(0); Hz.fill(0); Ex.fill(0); Ey.fill(0); rxBuf.fill(0);
      };
    });
  }
  var re = new Float32Array(N), im = new Float32Array(N), hann = new Float32Array(N), spec = new Float32Array(N / 2);
  for (var h0 = 0; h0 < N; h0++) hann[h0] = 0.5 - 0.5 * Math.cos((2 * Math.PI * h0) / (N - 1));

  function fft(re, im) {
    var len, i, j = 0, k;
    for (i = 1; i < N; i++) {
      var bit = N >> 1;
      for (; j & bit; bit >>= 1) j ^= bit;
      j ^= bit;
      if (i < j) { var t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; }
    }
    for (len = 2; len <= N; len <<= 1) {
      var ang = (-2 * Math.PI) / len, wr = Math.cos(ang), wi = Math.sin(ang);
      for (i = 0; i < N; i += len) {
        var cr = 1, ci = 0;
        for (k = 0; k < len / 2; k++) {
          var a = i + k, b = a + len / 2;
          var xr = re[b] * cr - im[b] * ci, xi = re[b] * ci + im[b] * cr;
          re[b] = re[a] - xr; im[b] = im[a] - xi; re[a] += xr; im[a] += xi;
          var nr = cr * wr - ci * wi; ci = cr * wi + ci * wr; cr = nr;
        }
      }
    }
  }

  var ampAvg = 0, phAvg = 0, dopAvg = 0, lastR = null, lastStep = 0;
  function analyze() {
    if (!panel) return;
    var i;
    for (i = 0; i < N; i++) { var k = (bi + i) % N; re[i] = rxBuf[k] * hann[i]; im[i] = 0; }
    fft(re, im);
    var mx = 1e-12;
    for (i = 0; i < N / 2; i++) { spec[i] = Math.hypot(re[i], im[i]); if (spec[i] > mx) mx = spec[i]; }

    // I/Q over the last four carrier cycles, referenced to the TX
    var I = 0, Q = 0, TI = 0, TQ = 0, M = 144;
    for (var j = 0; j < M; j++) {
      var k2 = (bi - 1 - j + N) % N, ang2 = 2 * Math.PI * F0 * j;
      I += rxBuf[k2] * Math.cos(ang2); Q += rxBuf[k2] * Math.sin(ang2);
      TI += txBuf[k2] * Math.cos(ang2); TQ += txBuf[k2] * Math.sin(ang2);
    }
    var tn = Math.hypot(TI, TQ) || 1;
    var zr = (I * TI + Q * TQ) / (tn * M), zi = (Q * TI - I * TQ) / (tn * M);
    ampAvg += (Math.hypot(zr, zi) - ampAvg) * 0.2;
    phAvg = Math.atan2(zi, zr);

    // bistatic Doppler: fd = -f0 · (dR/dt) / c,  R = |TX→reflector| + |reflector→RX|
    var R = refl.on ? Math.hypot(refl.x - tx.x, refl.y - tx.y) + Math.hypot(refl.x - rx.x, refl.y - rx.y) : null;
    if (R !== null && lastR !== null && step > lastStep) {
      var fd = Math.max(-0.9, Math.min(0.9, -((R - lastR) / (step - lastStep)) / S));
      dopAvg += (fd - dopAvg) * 0.35;
    } else dopAvg *= 0.8;
    lastR = R; lastStep = step;

    var w = sc2.width, h = sc2.height, lo = Math.floor(F0 * 0.4 * N), hi = Math.ceil(F0 * 1.6 * N);
    sctx.clearRect(0, 0, w, h);
    sctx.strokeStyle = '#1e3a5a'; sctx.lineWidth = 1;
    for (var g = 1; g < 4; g++) { var gy = (h * g) / 4; sctx.beginPath(); sctx.moveTo(0, gy); sctx.lineTo(w, gy); sctx.stroke(); }
    var cx = ((F0 * N - lo) / (hi - lo)) * w;
    sctx.setLineDash([3, 3]); sctx.beginPath(); sctx.moveTo(cx, 0); sctx.lineTo(cx, h); sctx.stroke(); sctx.setLineDash([]);
    if (state.mode === 0 && Math.abs(dopAvg) > 0.005) {   // where the Doppler-shifted echo should sit
      var ex = ((F0 * (1 + dopAvg) * N - lo) / (hi - lo)) * w;
      sctx.strokeStyle = '#a78bfa'; sctx.lineWidth = 1.5; sctx.beginPath(); sctx.moveTo(ex, 0); sctx.lineTo(ex, h); sctx.stroke();
    }
    var grad = sctx.createLinearGradient(0, 0, 0, h);
    grad.addColorStop(0, 'rgba(0,229,255,0.45)'); grad.addColorStop(1, 'rgba(0,229,255,0)');
    sctx.beginPath(); sctx.moveTo(0, h);
    for (var b2 = lo; b2 <= hi; b2++) {
      var db = 20 * Math.log10(spec[b2] / mx + 1e-6);   // 0 … −60 dB
      sctx.lineTo(((b2 - lo) / (hi - lo)) * w, h - Math.max(0, (db + 60) / 60) * (h - 6));
    }
    sctx.lineTo(w, h); sctx.closePath(); sctx.fillStyle = grad; sctx.fill();
    sctx.strokeStyle = '#00e5ff'; sctx.lineWidth = 1.4; sctx.stroke();

    var dopMHz = dopAvg * 10000;   // carrier labelled 10 GHz
    read.amp.textContent = (20 * Math.log10(ampAvg + 1e-9)).toFixed(1) + ' dB';
    read.ph.textContent = ((phAvg * 180) / Math.PI).toFixed(0) + '°';
    read.dop.textContent = state.mode !== 0 ? '—' : Math.abs(dopMHz) < 5 ? '0 MHz'
      : Math.abs(dopMHz) >= 1000 ? (dopMHz / 1000).toFixed(2) + ' GHz' : dopMHz.toFixed(0) + ' MHz';
    read.mode.textContent = MODES[state.mode];
  }

  /* ── input ── */
  function point(x, y) {
    mouse.x = x; mouse.y = y;
    if (!refl.on) { refl.x = x / CELL; refl.y = y / CELL; refl.on = true; }
  }
  window.addEventListener('mousemove', function (e) {
    point(e.clientX, e.clientY);
    if (drawing) { paintPath([[drawing.x, drawing.y], [e.clientX, e.clientY]], drawing.id); drawing.x = e.clientX; drawing.y = e.clientY; }
    if (preview) preview.b = [e.clientX, e.clientY];
  }, { passive: true });

  // Right-click and drag on the page background draws; with the draw palette open, left-drag does too.
  var INTERACTIVE = 'a,button,input,textarea,select,label,img,video,canvas,.pcb3d,.rf-spec,.rf-draw';
  var paletteOpen = false;
  function onBackground(el) { return !(el && el.closest && el.closest(INTERACTIVE)); }
  window.addEventListener('mousedown', function (e) {
    var ok = (e.button === 2 || (e.button === 0 && paletteOpen)) && onBackground(e.target);
    if (!ok) return;
    if (e.button === 0) e.preventDefault();   // no text selection while drawing
    var pt = [e.clientX, e.clientY];
    if (brush.tool === 'free') {
      drawing = { x: pt[0], y: pt[1], id: ++strokeId, btn: e.button };
      strokeStack.push(drawing.id);
      paintPath([pt], drawing.id);
    } else preview = { tool: brush.tool, a: pt, b: pt, btn: e.button };
  });
  window.addEventListener('mouseup', function (e) {
    if (drawing && e.button === drawing.btn) drawing = null;
    if (preview && e.button === preview.btn) { commitShape(preview.tool, preview.a, preview.b); preview = null; }
  });
  window.addEventListener('blur', function () { drawing = null; preview = null; });
  window.addEventListener('contextmenu', function (e) { if (onBackground(e.target)) e.preventDefault(); });

  /* ── draw palette ── */
  var LIVES = [[1, '1 s'], [3, '3 s'], [8, '8 s'], [20, '20 s'], [Infinity, '∞']];
  var pal = document.createElement('div');
  pal.className = 'rf-draw';
  pal.innerHTML =
    '<button type="button" class="rf-draw-toggle" aria-expanded="false" title="Draw into the field (right-drag works any time)">✎ draw</button>' +
    '<div class="rf-draw-panel" hidden>' +
    '<div class="rf-draw-row"><span>tool</span><div class="seg" data-g="tool">' +
    '<button data-v="free" class="on" title="Freehand">free</button><button data-v="line" title="Straight line">line</button>' +
    '<button data-v="ring" title="Ring: drag out the radius">ring</button><button data-v="dish" title="Parabolic dish: press at the focus, drag to the vertex. Comes with a feed antenna.">dish</button>' +
    '<button data-v="antenna" title="Drop an extra antenna that radiates the TX waveform">antenna</button></div></div>' +
    '<div class="rf-draw-row"><span>material</span><div class="seg" data-g="mat">' +
    '<button data-v="0" class="on" title="Perfect conductor: reflects">metal</button><button data-v="1" title="Lossy absorber: soaks waves up">absorber</button>' +
    '<button data-v="2" title="Dielectric, εr = 4: slows waves, so it refracts and focuses">glass</button></div></div>' +
    '<div class="rf-draw-row"><span>size</span><input type="range" min="1" max="8" step="0.2" value="2.6" data-g="size"><em data-r="size"></em></div>' +
    '<div class="rf-draw-row"><span>lifetime</span><div class="seg" data-g="life">' +
    LIVES.map(function (l) { return '<button data-v="' + l[0] + '"' + (l[0] === 3 ? ' class="on"' : '') + '>' + l[1] + '</button>'; }).join('') + '</div></div>' +
    '<div class="rf-draw-row"><span>symmetry</span><div class="seg" data-g="sym">' +
    '<button data-v="none" class="on">off</button><button data-v="mirror">mirror</button><button data-v="quad">4-way</button><button data-v="radial">6-way</button></div></div>' +
    '<div class="rf-draw-row rf-draw-act"><button type="button" data-act="undo">undo (Z)</button><button type="button" data-act="clear">clear (C)</button></div>' +
    '<p>Left- or right-drag on the background. Keys: [ ] size · 1 2 3 material · Z undo · C clear · Esc close.</p>' +
    '</div>';
  document.body.appendChild(pal);
  var panelEl = pal.querySelector('.rf-draw-panel'), toggleEl = pal.querySelector('.rf-draw-toggle');
  var sizeEl = pal.querySelector('[data-g="size"]'), sizeOut = pal.querySelector('[data-r="size"]');
  function showSize() { sizeOut.textContent = Math.round(brush.size * 2 * CELL) + ' px'; sizeEl.value = brush.size; }
  function setOpen(o) {
    paletteOpen = o; panelEl.hidden = !o; toggleEl.setAttribute('aria-expanded', o);
    document.body.classList.toggle('rf-drawing', o);
  }
  function pick(group, v) {
    pal.querySelectorAll('[data-g="' + group + '"] button').forEach(function (b) { b.classList.toggle('on', b.dataset.v === String(v)); });
  }
  toggleEl.onclick = function () { setOpen(!paletteOpen); };
  pal.querySelectorAll('.seg[data-g] button').forEach(function (b) {
    b.type = 'button';
    b.onclick = function () {
      var g = b.parentNode.dataset.g, v = b.dataset.v;
      if (g === 'tool') brush.tool = v;
      if (g === 'mat') brush.mat = +v;
      if (g === 'life') brush.life = v === 'Infinity' ? Infinity : +v;
      if (g === 'sym') brush.sym = v;
      pick(g, v);
    };
  });
  sizeEl.oninput = function () { brush.size = +sizeEl.value; showSize(); };
  pal.querySelector('[data-act="undo"]').onclick = undo;
  pal.querySelector('[data-act="clear"]').onclick = clearAll;
  showSize();
  window.addEventListener('keydown', function (e) {
    if (!paletteOpen || e.ctrlKey || e.metaKey || e.altKey || /INPUT|TEXTAREA|SELECT/.test(e.target.tagName)) return;
    var k = e.key.toLowerCase();
    if (k === '[') { brush.size = Math.max(1, brush.size - 0.4); showSize(); }
    else if (k === ']') { brush.size = Math.min(8, brush.size + 0.4); showSize(); }
    else if (k === '1' || k === '2' || k === '3') { brush.mat = +k - 1; pick('mat', brush.mat); }
    else if (k === 'z') undo();
    else if (k === 'c') clearAll();
    else if (k === 'escape') setOpen(false);
    else return;
    e.preventDefault();
  });

  window.addEventListener('touchmove', function (e) { var t = e.touches[0]; if (t) point(t.clientX, t.clientY); }, { passive: true });
  document.documentElement.addEventListener('mouseleave', function () { refl.on = false; });

  var resizeT;
  window.addEventListener('resize', function () { clearTimeout(resizeT); resizeT = setTimeout(setup, 150); });

  setup();
  var frame = 0;
  (function loop() {
    requestAnimationFrame(loop);
    if (document.hidden) return;
    var fade = Math.max(0.35, 1 - window.scrollY / (window.innerHeight * 1.2));
    var t0 = performance.now();
    solve();
    // keep frames on time: fewer solver steps per frame on slow machines, more when there is room
    solveMs += (performance.now() - t0 - solveMs) * 0.05;
    if (frame % 60 === 59) {
      if (solveMs > 10 && STEPS > 1) STEPS--;
      else if (solveMs < 4.5 && STEPS < MAX_STEPS) STEPS++;
    }
    draw(fade);
    drawOverlay(fade);
    if (++frame % 4 === 0 && window.scrollY < window.innerHeight * 1.5) analyze();
  })();
  window.rfField = state;   // handy for debugging from the console
})();
