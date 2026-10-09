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
  var reduce = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  var CELL = 6;                 // css px per Yee cell
  var S = 0.5;                  // Courant number c·dt/dx (2D limit is 1/sqrt 2)
  var STEPS = reduce ? 1 : 2;   // solver steps per frame
  var SPONGE = 30;              // graded absorbing border (cells)
  var F0 = 1 / 36;              // carrier, cycles per step  ->  lambda = S/F0 = 18 cells
  var N = 1024;                 // RX record length for the FFT
  var ARROW = 6;                // cells between in-plane field arrows

  var MODES = ['CW', 'FMCW', 'PULSE'];
  var POLS = { tm: 'TMz · E ⊥ screen', te: 'TEz · E in plane', circ: 'Circular · TM + TE at 90°' };
  var state = { pol: 'tm', view: 'E', mode: 0 };

  var W, H, n, damp, wall, img, off, offCtx;
  var Ez, Hx, Hy, Hz, Ex, Ey;
  var tx = {}, rx = {}, posts = [];
  var refl = { x: 0, y: 0, r: 4.5, on: false };
  var mouse = { x: -1, y: -1 };
  var step = 0, phase = 0, gain = 30;
  var rxBuf = new Float32Array(N), txBuf = new Float32Array(N), bi = 0;

  function setup() {
    var vw = window.innerWidth, vh = window.innerHeight;
    canvas.width = vw; canvas.height = vh;
    W = Math.ceil(vw / CELL) + 2; H = Math.ceil(vh / CELL) + 2; n = W * H;
    Ez = new Float32Array(n); Hx = new Float32Array(n); Hy = new Float32Array(n);
    Hz = new Float32Array(n); Ex = new Float32Array(n); Ey = new Float32Array(n);
    damp = new Float32Array(n); wall = new Uint8Array(n);
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
    if (refl.on) stamp(refl, 1);
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
    if (!v) posts.forEach(function (p) { if (p !== o) stamp(p, 1); });
  }

  function txSample(offset) {
    var a = 1;
    if (state.mode === 2) { var k = step % 420; a = Math.exp(-Math.pow((k - 40) / 14, 2)); } // gaussian pulses
    return a * Math.sin(phase + offset);
  }

  function moveReflector() {
    if (!refl.on) return;
    var tx_ = mouse.x / CELL, ty_ = mouse.y / CELL;
    var dx = tx_ - refl.x, dy = ty_ - refl.y, dist = Math.hypot(dx, dy);
    if (dist < 0.05) return;
    stamp(refl, 0);
    if (dist > 60) { refl.x = tx_; refl.y = ty_; }
    else {
      // eased chase, capped below the wave speed so the scattering stays physical
      var mv = Math.min(dist * 0.25, 0.22 * STEPS);
      refl.x += (dx / dist) * mv; refl.y += (dy / dist) * mv;
    }
    stamp(refl, 1);
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
      Ez[i] = (Ez[i] + S * ((Hy[i] - Hy[i - 1]) - (Hx[i] - Hx[i - W]))) * damp[i];
    }
    var t = tx.y * W + tx.x;
    Ez[t] += src; Ez[t + 1] += src * 0.5; Ez[t - 1] += src * 0.5;
  }

  function stepTE(src) {
    var x, y, i;
    for (y = 1; y < H - 1; y++) for (x = 1; x < W - 1; x++) {
      i = y * W + x;
      if (wall[i]) { Ex[i] = Ey[i] = 0; continue; }   // PEC: in-plane E vanishes
      Ex[i] = (Ex[i] + S * (Hz[i] - Hz[i - W])) * damp[i];
      Ey[i] = (Ey[i] - S * (Hz[i] - Hz[i - 1])) * damp[i];
    }
    for (y = 0; y < H - 1; y++) for (x = 0; x < W - 1; x++) {
      i = y * W + x;
      Hz[i] = (Hz[i] - S * ((Ey[i + 1] - Ey[i]) - (Ex[i + W] - Ex[i]))) * damp[i];
    }
    var t = tx.y * W + tx.x;
    Hz[t] += src; Hz[t + 1] += src * 0.5; Hz[t - 1] += src * 0.5;
  }

  function solve() {
    moveReflector();
    var tm = state.pol !== 'te', te = state.pol !== 'tm';
    for (var s = 0; s < STEPS; s++) {
      var f = state.mode === 1 ? F0 * (0.75 + 0.5 * ((step % 900) / 900)) : F0;   // FMCW: sawtooth chirp
      phase += 2 * Math.PI * f;
      var a = txSample(0), b = txSample(Math.PI / 2);
      if (tm) stepTM(a * 0.5);
      if (te) stepTE((state.pol === 'circ' ? b : a) * 0.5);
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
    if (refl.on) {
      ctx.globalAlpha = 0.9 * fade;
      ctx.strokeStyle = '#e2e8f0';
      ctx.beginPath(); ctx.arc(refl.x * CELL + CELL / 2, refl.y * CELL + CELL / 2, refl.r * CELL, 0, Math.PI * 2); ctx.stroke();
    }
    ctx.globalAlpha = 1;
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
      dopAvg += (-((R - lastR) / (step - lastStep)) / S - dopAvg) * 0.35;
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
    if (!refl.on) { refl.x = x / CELL; refl.y = y / CELL; refl.on = true; stamp(refl, 1); }
  }
  window.addEventListener('mousemove', function (e) { point(e.clientX, e.clientY); }, { passive: true });
  window.addEventListener('touchmove', function (e) { var t = e.touches[0]; if (t) point(t.clientX, t.clientY); }, { passive: true });
  document.documentElement.addEventListener('mouseleave', function () { if (refl.on) { stamp(refl, 0); refl.on = false; } });

  var resizeT;
  window.addEventListener('resize', function () { clearTimeout(resizeT); resizeT = setTimeout(setup, 150); });

  setup();
  var frame = 0;
  (function loop() {
    requestAnimationFrame(loop);
    if (document.hidden) return;
    var fade = Math.max(0.35, 1 - window.scrollY / (window.innerHeight * 1.2));
    solve();
    draw(fade);
    if (++frame % 4 === 0 && window.scrollY < window.innerHeight * 1.5) analyze();
  })();
  window.rfField = state;   // handy for debugging from the console
})();
