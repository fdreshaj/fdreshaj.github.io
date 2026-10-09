/* Exploded PCB layer viewer.
   Each board folder (layers/<id>/) holds board.json plus one WebP texture per layer,
   generated from the KiCad .kicad_pcb files. Markup:
   <div class="pcb3d" data-boards="vna:HUBRIS VNA,vco:VCO board"></div> */
(function () {
  var THREE_URL = 'js/vendor/three-r128.min.js';
  var threeReady = null;

  function loadThree() {
    if (window.THREE) return Promise.resolve();
    if (!threeReady) {
      threeReady = new Promise(function (res, rej) {
        var s = document.createElement('script');
        s.src = THREE_URL; s.onload = res; s.onerror = rej;
        document.head.appendChild(s);
      });
    }
    return threeReady;
  }

  var KIND = {
    silk: { opacity: 1, alphaTest: 0.3, swatch: '#f0f0eb' },
    mask: { opacity: 0.72, alphaTest: 0.02, swatch: '#16a34a' },
    cu: { opacity: 1, alphaTest: 0.3, swatch: '#d6a048' },
    core: { opacity: 0.45, alphaTest: 0.02, swatch: '#bea96e' }
  };

  function ease(t) { return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2; }

  function Viewer(root) {
    this.root = root;
    this.boards = root.dataset.boards.split(',').map(function (s) {
      var p = s.split(':'); return { id: p[0].trim(), label: (p[1] || p[0]).trim() };
    });
    this.t = 0; this.auto = true; this.visible = false; this.az = -0.6; this.el = 0.55;
    this.buildDom();
  }

  Viewer.prototype.buildDom = function () {
    var self = this, r = this.root;
    r.innerHTML =
      '<div class="pcb3d-stage"><canvas></canvas><div class="pcb3d-status">loading layers…</div>' +
      '<div class="pcb3d-hint">drag to rotate · hover a layer to isolate it · click to hide</div></div>' +
      '<div class="pcb3d-bar">' +
      (this.boards.length > 1 ? '<div class="pcb3d-tabs"></div>' : '') +
      '<div class="pcb3d-ctrl"><button type="button" class="pcb3d-play">▶ replay</button>' +
      '<label>assembled<input type="range" min="0" max="1000" value="0"></label>exploded</div>' +
      '<ul class="pcb3d-legend"></ul></div>';
    this.canvas = r.querySelector('canvas');
    this.status = r.querySelector('.pcb3d-status');
    this.slider = r.querySelector('input');
    this.legend = r.querySelector('.pcb3d-legend');
    if (this.boards.length > 1) {
      var tabs = r.querySelector('.pcb3d-tabs');
      this.boards.forEach(function (b, i) {
        var bt = document.createElement('button');
        bt.type = 'button'; bt.textContent = b.label;
        bt.onclick = function () { self.load(i); };
        tabs.appendChild(bt);
      });
    }
    r.querySelector('.pcb3d-play').onclick = function () { self.replay(); };
    this.slider.oninput = function () { self.auto = false; self.t = this.value / 1000; self.layout(); };

    var drag = null;
    this.canvas.addEventListener('pointerdown', function (e) {
      drag = { x: e.clientX, y: e.clientY, az: self.az, el: self.el };
      self.canvas.setPointerCapture(e.pointerId); self.spin = false;
    });
    this.canvas.addEventListener('pointermove', function (e) {
      if (!drag) return;
      self.az = drag.az - (e.clientX - drag.x) * 0.008;
      self.el = Math.max(0.08, Math.min(1.5, drag.el + (e.clientY - drag.y) * 0.006));
    });
    this.canvas.addEventListener('pointerup', function () { drag = null; });
  };

  Viewer.prototype.start = function () {
    var self = this;
    if (this.started) { this.visible = true; return; }
    this.started = true; this.visible = true;
    loadThree().then(function () { self.init(); self.load(0); })
      .catch(function () { self.status.textContent = 'could not load the 3D viewer'; });
  };

  Viewer.prototype.init = function () {
    var T = window.THREE;
    this.renderer = new T.WebGLRenderer({ canvas: this.canvas, antialias: true, alpha: true });
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    this.renderer.outputEncoding = T.sRGBEncoding;
    this.scene = new T.Scene();
    this.camera = new T.PerspectiveCamera(32, 1.6, 1, 5000);
    this.group = new T.Group();
    this.scene.add(this.group);
    this.loop();
  };

  Viewer.prototype.load = function (i) {
    var self = this, T = window.THREE, b = this.boards[i];
    this.root.querySelectorAll('.pcb3d-tabs button').forEach(function (bt, k) { bt.classList.toggle('on', k === i); });
    this.status.style.display = ''; this.status.textContent = 'loading layers…';
    var base = 'layers/' + b.id + '/';
    fetch(base + 'board.json').then(function (r) { return r.json(); }).then(function (j) {
      var loader = new T.TextureLoader(), cache = {};
      var jobs = j.layers.map(function (l) {
        if (!cache[l.img]) {
          cache[l.img] = new Promise(function (res) {
            loader.load(base + l.img, function (tx) {
              tx.encoding = T.sRGBEncoding;
              tx.anisotropy = self.renderer.capabilities.getMaxAnisotropy();
              res(tx);
            }, undefined, function () { res(null); });
          });
        }
        return cache[l.img];
      });
      return Promise.all(jobs).then(function (tx) { self.build(j, tx); });
    }).catch(function () { self.status.textContent = 'could not load this board'; });
  };

  Viewer.prototype.build = function (j, tex) {
    var T = window.THREE, self = this;
    while (this.group.children.length) {
      var c = this.group.children.pop();
      if (c.geometry) c.geometry.dispose();
      if (c.material) c.material.dispose();
    }
    this.board = j;
    var span = Math.max(j.w, j.h);
    this.span = span;
    this.planes = [];
    var geo = new T.PlaneGeometry(j.w, j.h);
    j.layers.forEach(function (l, i) {
      var k = KIND[l.kind];
      var m = new T.MeshBasicMaterial({
        map: tex[i], transparent: true, opacity: k.opacity, alphaTest: k.alphaTest,
        side: T.DoubleSide, depthWrite: l.kind === 'cu' || l.kind === 'silk'
      });
      var mesh = new T.Mesh(geo, m);
      mesh.rotation.x = -Math.PI / 2;
      mesh.renderOrder = j.layers.length - i;
      mesh.userData = l;
      self.group.add(mesh);
      self.planes.push(mesh);
    });
    // index of each copper layer within the stack, for hole spans
    this.cuIdx = [];
    j.layers.forEach(function (l, i) { if (l.kind === 'cu') self.cuIdx.push(i); });

    var holeGeo = new T.CylinderGeometry(1, 1, 1, 14, 1, true);
    var plated = j.holes.filter(function (h) { return h[3]; });
    var npth = j.holes.filter(function (h) { return !h[3]; });
    this.holeSets = [];
    [[plated, 0xe0b060], [npth, 0x2a2f3a]].forEach(function (p) {
      if (!p[0].length) return;
      var im = new T.InstancedMesh(holeGeo, new T.MeshBasicMaterial({ color: p[1], side: T.DoubleSide, transparent: true, opacity: 0.6, depthWrite: false }), p[0].length);
      self.group.add(im);
      self.holeSets.push({ mesh: im, holes: p[0] });
    });

    // legend
    this.legend.innerHTML = '';
    var seen = {};
    j.layers.forEach(function (l, i) {
      var li = document.createElement('li');
      li.innerHTML = '<span style="background:' + KIND[l.kind].swatch + '"></span>' + l.name;
      li.onmouseenter = function () { self.focus(i); };
      li.onmouseleave = function () { self.focus(-1); };
      li.onclick = function () { var p = self.planes[i]; p.visible = !p.visible; li.classList.toggle('off', !p.visible); };
      self.legend.appendChild(li);
    });
    var drills = j.holes.length;
    var info = document.createElement('li');
    info.className = 'pcb3d-meta';
    info.textContent = j.copper + '-layer · ' + j.w.toFixed(1) + ' × ' + j.h.toFixed(1) + ' mm · ' + drills + ' drill holes';
    this.legend.appendChild(info);

    this.status.style.display = 'none';
    this.replay();
  };

  Viewer.prototype.focus = function (i) {
    this.planes.forEach(function (p, k) {
      var base = KIND[p.userData.kind].opacity;
      p.material.opacity = i < 0 || k === i ? base : base * 0.12;
    });
  };

  Viewer.prototype.replay = function () {
    this.auto = true; this.t0 = performance.now(); this.t = 0; this.spin = true;
    this.az = -0.6; this.el = 0.55; this.layout();
  };

  Viewer.prototype.layout = function () {
    if (!this.board) return;
    var T = window.THREE, j = this.board, n = j.layers.length;
    var e = ease(this.t);
    // assembled: true stack (thickness exaggerated so it reads as a board); exploded: even gaps
    var thick = Math.max(j.thickness, 1.6) * 1.6;
    var gap = (this.span * 0.6) / (n - 1);
    var ys = [];
    for (var i = 0; i < n; i++) {
      var a = thick / 2 - (thick * i) / (n - 1);
      var x = (gap * (n - 1)) / 2 - gap * i;
      ys.push(a + (x - a) * e);
    }
    this.planes.forEach(function (p, i) { p.position.y = ys[i]; });
    var cu = this.cuIdx, cx = j.w / 2, cz = j.h / 2, mtx = new T.Matrix4(), q = new T.Quaternion(), s = new T.Vector3(), pos = new T.Vector3();
    this.holeSets.forEach(function (set) {
      set.holes.forEach(function (h, k) {
        var top = ys[cu[Math.min(h[4], cu.length - 1)]], bot = ys[cu[Math.min(h[5], cu.length - 1)]];
        // through holes also pierce mask and silk
        if (h[4] === 0) top = ys[0];
        if (h[5] >= cu.length - 1) bot = ys[n - 1];
        var r = Math.max(h[2] / 2, 0.08);
        pos.set(h[0] - cx, (top + bot) / 2, h[1] - cz);
        s.set(r, Math.max(top - bot, 0.05), r);
        mtx.compose(pos, q, s);
        set.mesh.setMatrixAt(k, mtx);
      });
      set.mesh.instanceMatrix.needsUpdate = true;
    });
    this.slider.value = Math.round(this.t * 1000);
  };

  Viewer.prototype.loop = function () {
    var self = this;
    requestAnimationFrame(function () { self.loop(); });
    if (!this.board || !this.visible) return;
    var rc = this.canvas.getBoundingClientRect();
    if (rc.bottom < 0 || rc.top > window.innerHeight || rc.height < 10) return;
    var now = performance.now();
    if (this.auto) {
      var k = (now - this.t0) / 1000;
      var t = Math.min(1, Math.max(0, (k - 0.9) / 2.4));
      if (t !== this.t) { this.t = t; this.layout(); }
      if (t >= 1) this.auto = false;
    }
    if (this.spin) this.az += 0.0025;
    var w = this.canvas.clientWidth, h = this.canvas.clientHeight;
    if (this.canvas.width !== Math.round(w * this.renderer.getPixelRatio())) {
      this.renderer.setSize(w, h, false);
      this.camera.aspect = w / h; this.camera.updateProjectionMatrix();
    }
    var d = this.span * (2.0 + 0.5 * ease(this.t)) / Math.min(1, this.camera.aspect / 1.3);
    this.camera.position.set(Math.sin(this.az) * Math.cos(this.el) * d, Math.sin(this.el) * d, Math.cos(this.az) * Math.cos(this.el) * d);
    this.camera.lookAt(0, 0, 0);
    this.renderer.render(this.scene, this.camera);
  };

  var viewers = [];
  document.querySelectorAll('.pcb3d').forEach(function (el) {
    var v = new Viewer(el); el._viewer = v; viewers.push(v);
  });

  // Start a viewer when its project opens; pause the others.
  window.pcb3dOnToggle = function (item, open) {
    item.querySelectorAll('.pcb3d').forEach(function (el) {
      if (open) el._viewer.start(); else el._viewer.visible = false;
    });
  };
  // Viewers already visible on load (e.g. an item rendered open)
  document.querySelectorAll('.proj-item.open .pcb3d').forEach(function (el) { el._viewer.start(); });
})();
