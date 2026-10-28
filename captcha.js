/* captcha.js - protection plan Step 8: the game captcha on screen.
   Loaded only when the server asks for it (index.html adds <script src="/captcha.js"> on demand) and by /captcha-lab.
   Part 1  maths    - the SAME formulas as captcha.py (test_step7/8 compare both on hundreds of shots).
   Part 2  CapShooter - pointer -> shots, no DOM (so it is testable): aim, 0.4 s rule, samples a hand makes.
   Part 3  proof-of-work - small sha256, solved in the background while the player plays.
   Part 4  CapGame  - the canvas card: CapGame.modal(opts) for the site, CapGame.run(host, opts) for the lab.
   Everything is drawn on ONE canvas: there is no ball element in the page for a script to read.
   Server contract: POST /api/captcha/new  ->  {id, ttl, cfg, game:{type,balls,targets,skews}, pow:{salt,bits}}
                    POST /api/captcha/verify {id, pow, shots:[{t,a,s:[[t,a]..]}]} -> {ok, token, ttl} | {ok:false, why} */
(function (root) {
"use strict";
const CAP = { W: 360, H: 300, CX: 180, CY: 284, BR: 5, STEP: 8, NCOL: 4 };

/* ------------------------------------------------------------ part 1: maths (= captcha.py) */
function capTri(x) { const f = x - Math.floor(x); return 4 * Math.abs(f - 0.5) - 1; }
function capBallPos(game, i, tMs, cfg) {
  const p = game.balls[i], T = 2 * Math.PI, ty = p.ty === undefined ? game.type : p.ty; let u = tMs / 1000 * cfg.speed; if (ty !== 1) u *= (p.dir || 1);
  let x, y;
  if (ty === 0) { x = 180 + 118 * capTri(u * p.f + p.ph / T); y = p.y + 20 * Math.sin(u * p.g + p.ph2); }
  else if (ty === 1) { const a = u * p.f * p.dir + p.ph; x = 180 + p.rx * Math.cos(a); y = 110 + p.ry * Math.sin(a); }
  else if (ty === 2) { x = 180 + 125 * Math.sin(u * p.f + p.ph); y = 105 + 55 * Math.sin(u * p.g + p.ph2); }
  else { const a = u * p.f + p.ph; x = 180 + 122 * Math.sin(a); y = 105 + p.ry * Math.sin(2 * a + p.ph2); }
  if (p.wa !== undefined) { x += p.wa * Math.sin(u * p.wf + p.wp); y += p.wb * Math.sin(u * p.wg + p.wq); }
  return [x, Math.max(y, 32)];
}
function capBallColor(game, i, tMs, cfg) { return game.balls[i].c % CAP.NCOL; }
/* shot k fired at tMs with finger angle a; the bullet really flies along a + skews[k] */
function capSimShot(game, cfg, k, tMs, a) {
  const ang = a + game.skews[k], dx = Math.sin(ang), dy = -Math.cos(ang), vb = cfg.bullet;
  const reach = cfg.size + CAP.BR + (cfg.slack === undefined ? 3 : cfg.slack);
  let ms = Math.round(tMs); const end = ms + Math.trunc(1000 * 340 / vb);
  while (ms <= end) {
    const d = vb * (ms - tMs) / 1000, bx = CAP.CX + dx * d, by = CAP.CY + dy * d;
    if (bx < -CAP.BR || bx > CAP.W + CAP.BR || by < -CAP.BR) break;
    let best = -1, bd = 1e18;
    for (let i = 0; i < game.balls.length; i++) {
      const q = capBallPos(game, i, ms, cfg), dd = (q[0] - bx) * (q[0] - bx) + (q[1] - by) * (q[1] - by);
      if (dd <= reach * reach && dd < bd) { best = i; bd = dd; }
    }
    if (best >= 0) return { hit: best, t: ms, color: capBallColor(game, best, ms, cfg) };
    ms += CAP.STEP;
  }
  return { hit: -1, t: null, color: null };
}
/* the finger -> angle.  Thumb anywhere in the lower half; +70 keeps it calm when the thumb is level with the cannon */
function capAim(px, py) { return Math.max(-1.3, Math.min(1.3, Math.atan2(px - CAP.CX, (CAP.CY - py) + 70))); }

/* ------------------------------------------------------------ part 2: pointer -> shots (no DOM) */
class CapShooter {
  constructor(game, cfg) { this.g = game; this.c = cfg; this.hits = 0; this.k = 0; this.shots = []; this.prevT = 0; this.drag = false; this.s = []; this.a = 0; }
  target() { return this.g.targets[Math.min(this.hits, this.g.targets.length - 1)]; }
  done() { return this.hits >= this.c.hits; }
  exhausted() { return !this.done() && this.k >= this.c.max_shots; }
  /* thumb down: only the lower half of the card counts (the upper half stays free for the eyes) */
  down(px, py, t) { if (this.done() || this.exhausted() || py < CAP.H * 0.5) return false; this.drag = true; this.a = capAim(px, py); this.s = [[t, this.a]]; return true; }
  move(px, py, t) { if (!this.drag) return; this.a = capAim(px, py); this.s.push([t, this.a]); if (this.s.length > 80) this.s.splice(0, 40); }
  /* thumb up = shot.  -> null (nothing) | {early:true} | {shot, res, ok} */
  up(px, py, t) {
    if (!this.drag) return null; this.drag = false;
    const a = capAim(px, py), tt = Math.round(t);
    if (tt - this.prevT < this.c.min_shot_ms) return { early: true };
    const s = this.s.filter(p => p[0] >= tt - 2000); s.push([t, a]);
    const shot = { t: tt, a: a, s: s.slice(-40).map(p => [Math.round(p[0] * 10) / 10, Math.round(p[1] * 1e5) / 1e5]) };
    const k = this.k, want = this.target(), res = capSimShot(this.g, this.c, k, tt, a);
    const ok = res.hit >= 0 && res.color === want;
    this.shots.push(shot); this.prevT = tt; this.k++; this.hits += ok ? 1 : 0;
    return { shot, res, ok, want, k };
  }
  body(id, pow, lab) { const b = { id: id, pow: pow, shots: this.shots }; if (lab) b.lab = true; return b; }
}

/* tap mode: tap the ball that has the asked colour (same maths as captcha.py replay_tap) */
class CapTapper {
  constructor(game, cfg) { this.g = game; this.c = cfg; this.hits = 0; this.k = 0; this.shots = []; this.prevT = 0; this.drag = false; }
  target() { return this.g.targets[Math.min(this.hits, this.g.targets.length - 1)]; }
  done() { return this.hits >= this.c.hits; }
  exhausted() { return !this.done() && this.k >= this.c.max_shots; }
  tap(px, py, t) {
    if (this.done() || this.exhausted()) return null;
    const tt = Math.round(t); if (tt - this.prevT < this.c.min_shot_ms) return { early: true };
    const want = this.target(), reach = this.c.size + (this.c.slack === undefined ? 3 : this.c.slack); let best = -1, bd = 1e18;
    for (let i = 0; i < this.g.balls.length; i++) { const q = capBallPos(this.g, i, tt, this.c), dd = (q[0] - px) * (q[0] - px) + (q[1] - py) * (q[1] - py); if (dd <= reach * reach && dd < bd) { best = i; bd = dd; } }
    const color = best >= 0 ? capBallColor(this.g, best, tt, this.c) : null, ok = best >= 0 && color === want, k = this.k;
    this.shots.push({ t: tt, x: Math.round(px * 100) / 100, y: Math.round(py * 100) / 100 }); this.prevT = tt; this.k++; this.hits += ok ? 1 : 0;
    return { shot: this.shots[k], res: { hit: best, t: tt, color: color }, ok, want, k };
  }
  body(id, pow, lab) { const b = { id: id, pow: pow, shots: this.shots }; if (lab) b.lab = true; return b; }
}

/* ------------------------------------------------------------ part 3: proof-of-work */
const K = new Uint32Array([0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]);
const W32 = new Uint32Array(64);
/* sha256 of an ASCII string (up to 55 bytes = one block, enough for "<id>:<salt>:<nonce>") -> Uint32Array(8) */
function capSha256(str) {
  const n = str.length, b = new Uint8Array(64);
  for (let i = 0; i < n; i++) b[i] = str.charCodeAt(i) & 255;
  b[n] = 0x80; b[62] = (n * 8 >>> 8) & 255; b[63] = (n * 8) & 255;
  for (let i = 0; i < 16; i++) W32[i] = (b[4 * i] << 24) | (b[4 * i + 1] << 16) | (b[4 * i + 2] << 8) | b[4 * i + 3];
  for (let i = 16; i < 64; i++) {
    const a = W32[i - 15], c = W32[i - 2];
    const s0 = ((a >>> 7) | (a << 25)) ^ ((a >>> 18) | (a << 14)) ^ (a >>> 3), s1 = ((c >>> 17) | (c << 15)) ^ ((c >>> 19) | (c << 13)) ^ (c >>> 10);
    W32[i] = (W32[i - 16] + s0 + W32[i - 7] + s1) | 0;
  }
  let h0 = 0x6a09e667, h1 = 0xbb67ae85, h2 = 0x3c6ef372, h3 = 0xa54ff53a, h4 = 0x510e527f, h5 = 0x9b05688c, h6 = 0x1f83d9ab, h7 = 0x5be0cd19;
  let A = h0, B = h1, C = h2, D = h3, E = h4, F = h5, G = h6, H = h7;
  for (let i = 0; i < 64; i++) {
    const S1 = ((E >>> 6) | (E << 26)) ^ ((E >>> 11) | (E << 21)) ^ ((E >>> 25) | (E << 7)), ch = (E & F) ^ (~E & G);
    const t1 = (H + S1 + ch + K[i] + W32[i]) | 0;
    const S0 = ((A >>> 2) | (A << 30)) ^ ((A >>> 13) | (A << 19)) ^ ((A >>> 22) | (A << 10)), mj = (A & B) ^ (A & C) ^ (B & C), t2 = (S0 + mj) | 0;
    H = G; G = F; F = E; E = (D + t1) | 0; D = C; C = B; B = A; A = (t1 + t2) | 0;
  }
  return new Uint32Array([(h0 + A) | 0, (h1 + B) | 0, (h2 + C) | 0, (h3 + D) | 0, (h4 + E) | 0, (h5 + F) | 0, (h6 + G) | 0, (h7 + H) | 0]);
}
function capZeroBits(w, bits) { if (bits <= 0) return true; if (bits <= 32) return (w[0] >>> (32 - bits)) === 0; return w[0] === 0 && (w[1] >>> (64 - bits)) === 0; }
function capPowOk(id, salt, bits, nonce) { return capZeroBits(capSha256(id + ":" + salt + ":" + nonce), bits); }
/* runs in slices of ~8 ms so the animation never stutters.  -> Promise<nonce string> */
function capSolvePow(id, salt, bits) {
  return new Promise(resolve => {
    let n = 0;
    (function slice() {
      const end = Date.now() + 8;
      while (Date.now() < end) { for (let j = 0; j < 200; j++, n++) if (capPowOk(id, salt, bits, n)) return resolve(String(n)); }
      setTimeout(slice, 0);
    })();
  });
}

/* ------------------------------------------------------------ part 4: the canvas card */
const COLS = [{ c: "#ef4444", n: "RED" }, { c: "#3b82f6", n: "BLUE" }, { c: "#22c55e", n: "GREEN" }, { c: "#facc15", n: "YELLOW" }];
function glyph(ctx, i, x, y, s, fill) {       /* a shape per colour too, so the game also works without telling colours apart */
  ctx.fillStyle = fill; ctx.beginPath();
  if (i === 0) { ctx.moveTo(x, y - s); ctx.lineTo(x + s, y + s * .8); ctx.lineTo(x - s, y + s * .8); }
  else if (i === 1) ctx.rect(x - s * .8, y - s * .8, s * 1.6, s * 1.6);
  else if (i === 2) ctx.arc(x, y, s * .85, 0, 6.2832);
  else { ctx.moveTo(x, y - s * 1.1); ctx.lineTo(x + s, y); ctx.lineTo(x, y + s * 1.1); ctx.lineTo(x - s, y); }
  ctx.closePath(); ctx.fill();
}
let cssDone = false;
function addCss() {
  if (cssDone || typeof document === "undefined") return; cssDone = true;
  const s = document.createElement("style");
  s.textContent = ".capov{position:fixed;left:0;top:0;right:0;bottom:0;z-index:99;background:rgba(0,0,0,.62);-webkit-backdrop-filter:blur(5px);backdrop-filter:blur(5px);display:flex;align-items:center;justify-content:center;padding:8px}"
    + ".capcard{width:min(94vw,440px);height:50vh;min-height:330px;max-height:560px;background:var(--panel,#17151a);border:1px solid var(--line,#2e2a33);border-radius:22px;box-shadow:0 20px 60px rgba(0,0,0,.5);display:flex;flex-direction:column;overflow:hidden;color:var(--text,#f1eef3);font:14px system-ui,sans-serif;user-select:none;-webkit-user-select:none}"
    + ".capcard.inl{height:460px;max-height:none;margin:0 auto}"
    + ".caph{display:flex;align-items:center;gap:10px;padding:0 6px 0 14px;height:52px;flex:none}"
    + ".capchip{width:22px;height:22px;border-radius:50%;flex:none;border:2px solid #fff}.capt{flex:1;font-weight:700;font-size:15px;min-width:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}"
    + ".capd{letter-spacing:3px;font-size:16px}.capx{width:48px;height:48px;border:0;background:transparent;color:inherit;font-size:22px;border-radius:14px}"
    + ".capcv{flex:1;display:flex;align-items:center;justify-content:center;min-height:0}.capcv canvas{touch-action:none;border-radius:14px;display:block}"
    + ".captx{width:100%;max-width:340px;padding:6px 14px;display:flex;flex-direction:column;gap:12px;user-select:text;-webkit-user-select:text}"
    + ".captx img{width:100%;height:auto;border-radius:12px;display:block;background:#eee;pointer-events:none}"
    + ".captx input{width:100%;box-sizing:border-box;font:700 22px/1 system-ui,sans-serif;letter-spacing:5px;text-align:center;text-transform:uppercase;padding:14px 10px;border-radius:14px;border:2px solid var(--line,#3a3442);background:rgba(255,255,255,.06);color:inherit;outline:0}"
    + ".captx input:focus{border-color:#ff5a2c}.captr{display:flex;gap:10px}.captr button{flex:1;height:48px;border-radius:14px;font:700 15px system-ui,sans-serif;border:0}"
    + ".captb{background:#ff5a2c;color:#fff}.captb2{background:rgba(255,255,255,.1);color:inherit}.captr button:disabled{opacity:.5}"
    + ".capm{height:34px;flex:none;text-align:center;font-size:13px;line-height:34px;opacity:.85;padding:0 10px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}";
  document.head.append(s);
}
function run(host, o) {
  o = o || {}; addCss();
  const D = document, st = { dead: false, game: null, cfg: null, id: null, sh: null, t0: 0, pow: null, phase: "load", bul: [], fx: [], thumb: null, aim: 0, hint: 1, flash: 0, autoT: 0 };
  const hd = D.createElement("div"); hd.className = "caph";
  const chip = D.createElement("div"); chip.className = "capchip"; chip.style.background = "#666";
  const ttl = D.createElement("div"); ttl.className = "capt"; ttl.textContent = "Loading…";
  const dots = D.createElement("div"); dots.className = "capd";
  const xb = D.createElement("button"); xb.className = "capx"; xb.textContent = "✕"; xb.setAttribute("aria-label", "Close");
  hd.append(chip, ttl, dots, xb);
  const cvw = D.createElement("div"); cvw.className = "capcv";
  const cv = D.createElement("canvas"), ctx = cv.getContext("2d"); cvw.append(cv);
  const msg = D.createElement("div"); msg.className = "capm";
  host.replaceChildren(hd, cvw, msg);
  const H = o.headers || {};
  async function post(url, body) {
    const ac = typeof AbortController !== "undefined" ? new AbortController() : null, tm = ac ? setTimeout(() => ac.abort(), 25000) : 0;   /* slow network: give up after 25 s instead of "Loading…" for ever */
    let r; try { r = await fetch(url, { method: "POST", headers: Object.assign({ "Content-Type": "application/json" }, H), body: JSON.stringify(body), signal: ac ? ac.signal : undefined }); } finally { clearTimeout(tm); }
    let j = {}; try { j = await r.json(); } catch (e) {} j._status = r.status; return j;
  }
  const say = t => { msg.textContent = t || ""; };
  let sc = 1;
  function layout() {
    const dpr = Math.min(2.5, root.devicePixelRatio || 1), aw = cvw.clientWidth - 8, ah = cvw.clientHeight - 4;
    const w = Math.max(120, Math.min(aw, ah * CAP.W / CAP.H)), hh = w * CAP.H / CAP.W;
    cv.style.width = w + "px"; cv.style.height = hh + "px"; cv.width = Math.round(w * dpr); cv.height = Math.round(hh * dpr); sc = cv.width / CAP.W;
  }
  const ro = typeof ResizeObserver !== "undefined" ? new ResizeObserver(layout) : null; if (ro) ro.observe(cvw); layout();

  async function start(note) {      /* any surprise while starting = a clear message + tap to retry, never "Loading…" for ever */
    try { await start0(note); } catch (e) {
      if (st.dead) return; st.phase = "err"; ttl.textContent = "Couldn't load"; chip.style.display = ""; say("Something went wrong - tap here to retry."); msg.style.cursor = "pointer";
      msg.onclick = () => { msg.onclick = null; msg.style.cursor = ""; start(); };
    }
  }
  async function start0(note) {
    st.phase = "load"; st.bul = []; st.fx = []; st.hint = 1; say(note || ""); ttl.textContent = "Loading…"; dots.textContent = ""; chip.style.display = "";
    if (!cvw.contains(cv)) cvw.replaceChildren(cv);
    const body = {}; if (o.lab) { body.lab = true; if (o.type !== undefined && o.type !== null && o.type !== "") body.type = +o.type; if (o.cfg) body.cfg = o.cfg; }
    let g; try { g = await post("/api/captcha/new", body); } catch (e) { g = {}; }
    if (st.dead) return;
    if (!g.id) { st.phase = "err"; ttl.textContent = "Couldn't load"; say(g._status === 429 ? "Too many tries - wait a minute, then tap here." : "Network problem - tap here to retry."); msg.style.cursor = "pointer"; msg.onclick = () => { msg.onclick = null; msg.style.cursor = ""; start(); }; return; }
    if (g.game && g.game.mode === "text") { textStart(g); return; }
    st.id = g.id; st.game = g.game; st.cfg = g.cfg; st.tap = g.game.mode === "tap"; st.sh = st.tap ? new CapTapper(g.game, g.cfg) : new CapShooter(g.game, g.cfg); st.pow = capSolvePow(g.id, g.pow.salt, g.pow.bits);
    st.t0 = performance.now(); st.phase = "play"; if (o.onStart) o.onStart(g); head(); say(st.tap ? "Read the question below, then tap the right ball." : "Thumb in the lower half: slide, then let go.");
  }
  /* picture captcha: letters drawn by the server, typed here.  The answer is never in the page - only the picture. */
  function textStart(g) {
    st.id = g.id; st.pow = capSolvePow(g.id, g.pow.salt, g.pow.bits); st.phase = "text"; st.t0 = performance.now();
    chip.style.display = "none"; ttl.textContent = "Quick check"; dots.textContent = "";
    const box = D.createElement("div"); box.className = "captx";
    const im = D.createElement("img"); im.src = g.game.img; im.alt = "Captcha picture"; im.draggable = false;
    const inp = D.createElement("input"); inp.type = "text"; inp.maxLength = 16; inp.autocomplete = "off"; inp.setAttribute("autocapitalize", "characters"); inp.setAttribute("autocorrect", "off"); inp.spellcheck = false; inp.setAttribute("aria-label", "Your answer"); inp.placeholder = "Your answer";
    const row = D.createElement("div"); row.className = "captr";
    const rf = D.createElement("button"); rf.type = "button"; rf.textContent = "↻ New picture"; rf.className = "captb2";
    const go = D.createElement("button"); go.type = "button"; go.textContent = "Verify"; go.className = "captb";
    row.append(rf, go); box.append(im, inp, row); cvw.replaceChildren(box);
    say("Do what the picture says. Several numbers? Put a space between them."); setTimeout(() => { try { inp.focus(); } catch (e) {} }, 60);
    async function sendText() {
      if (st.phase !== "text" || !inp.value.trim()) return; st.phase = "verify"; go.disabled = rf.disabled = inp.disabled = true; say("Checking…");
      const nonce = await st.pow; if (st.dead) return;
      let r; try { r = await post("/api/captcha/verify", { id: st.id, pow: nonce, text: inp.value, lab: o.lab ? true : undefined }); } catch (e) { r = { ok: false, why: "net" }; }
      if (st.dead) return;
      if (o.onVerified) o.onVerified(r, null);
      if (r.ok) { st.phase = "pass"; ttl.textContent = "Verified ✓"; say(""); if (o.onPass) o.onPass(r.token, r); return; }
      st.phase = "fail"; ttl.textContent = "Not quite"; say("Not right - here is a new picture."); st.autoT = setTimeout(() => start(), 900);
    }
    go.onclick = sendText; inp.addEventListener("keydown", e => { if (e.key === "Enter") { e.preventDefault(); sendText(); } });
    rf.onclick = () => { if (st.phase === "text") { st.phase = "wait"; start("New picture…"); } };
  }
  function head() {
    if (st.tap) { chip.style.display = "none"; ttl.textContent = "Quick check"; dots.textContent = ""; return; }   /* tap mode: the real question is drawn on the canvas only, not in the page text */
    const w = st.sh.target(); chip.style.background = COLS[w].c; ttl.textContent = (st.tap ? "Tap the " : "Shoot the ") + COLS[w].n + " ball";
    dots.textContent = Array.from({ length: st.cfg.hits }, (_, i) => i < st.sh.hits ? "●" : "○").join("");
  }
  async function submit() {
    st.phase = "verify"; say("Checking…");
    const nonce = await st.pow; if (st.dead) return;
    let r; try { r = await post("/api/captcha/verify", st.sh.body(st.id, nonce, o.lab)); } catch (e) { r = { ok: false, why: "net" }; }
    if (st.dead) return;
    if (o.onVerified) o.onVerified(r, st.sh);
    if (r.ok) { st.phase = "pass"; ttl.textContent = "Verified ✓"; say(""); if (o.onPass) o.onPass(r.token, r); return; }
    st.phase = "fail"; ttl.textContent = "Not quite";
    if (o.lab) { say("Server said: " + (r.real_why || r.why) + " - press 'New game' in the lab."); return; }
    say("Let's try a fresh one…"); st.autoT = setTimeout(() => start(), 900);
  }
  /* pointer -> game coordinates */
  function gxy(e) { const r = cv.getBoundingClientRect(); return [(e.clientX - r.left) / r.width * CAP.W, (e.clientY - r.top) / r.height * CAP.H]; }
  /* the touch's own timestamp (same clock as performance.now()): a thumb's samples then keep their real, uneven gaps instead of
     the even frame ticks; falls back to the clock when a browser gives something else */
  const now = e => { const n = performance.now(), x = e && e.timeStamp; return ((x > 0 && Math.abs(x - n) < 5000) ? x : n) - st.t0; };
  cv.addEventListener("pointerdown", e => {
    if (st.phase !== "play") return; e.preventDefault();
    const p = gxy(e);
    if (st.tap) {
      const r = st.sh.tap(p[0], p[1], now(e)); if (!r) return;
      if (r.early) { say("Wait a moment between taps."); return; }
      st.fx.push({ t: performance.now() - st.t0, ok: r.ok, p: [p[0], p[1]] }); head();
      say(r.res.hit < 0 ? "Missed - tap right on a ball." : r.ok ? "Hit!" : "Wrong ball - read the question again.");
      if (o.onShot) o.onShot({ k: r.k, t: r.shot.t, a: 0, hit: r.res.hit, color: r.res.color, want: r.want, ok: r.ok, hits: st.sh.hits, skew: 0 });
      if (st.sh.done()) setTimeout(submit, 450);
      else if (st.sh.exhausted()) { if (o.lab) setTimeout(submit, 450); else { st.phase = "wait"; say("Out of taps - fresh game…"); st.autoT = setTimeout(() => start(), 1100); } }
      return;
    }
    if (st.sh.down(p[0], p[1], now(e))) { try { cv.setPointerCapture(e.pointerId); } catch (_) {} st.thumb = p; st.aim = capAim(p[0], p[1]); st.hint = 0; }
    else { st.flash = performance.now(); say("Put your thumb in the lower half."); }
  });
  cv.addEventListener("pointermove", e => { if (st.phase !== "play" || !st.sh.drag) return; e.preventDefault(); const p = gxy(e); st.sh.move(p[0], p[1], now(e)); st.thumb = p; st.aim = capAim(p[0], p[1]); });
  const up = e => {
    if (st.tap || st.phase !== "play") return; const p = gxy(e), r = st.sh.up(p[0], p[1], now(e)); st.thumb = null; if (!r) return;
    if (r.early) { say("Wait a moment between shots."); return; }
    st.bul.push({ k: r.k, t: r.shot.t, ang: r.shot.a + st.game.skews[r.k], res: r.res, ok: r.ok });
    head(); say(r.res.hit < 0 ? "Missed - no ball there." : r.ok ? "Hit!" : "Wrong colour.");
    if (o.onShot) o.onShot({ k: r.k, t: r.shot.t, a: r.shot.a, hit: r.res.hit, color: r.res.color, want: r.want, ok: r.ok, hits: st.sh.hits, skew: st.game.skews[r.k] });
    if (st.sh.done()) setTimeout(submit, 450);
    else if (st.sh.exhausted()) { if (o.lab) setTimeout(submit, 450); else { st.phase = "wait"; say("Out of shots - fresh game…"); st.autoT = setTimeout(() => start(), 1100); } }
  };
  cv.addEventListener("pointerup", up); cv.addEventListener("pointercancel", up);
  xb.onclick = () => { if (o.onClose) o.onClose(); };

  /* drawing */
  function ball(x, y, r, col, big) {
    ctx.beginPath(); ctx.arc(x, y, r, 0, 6.2832); ctx.fillStyle = COLS[col].c; ctx.fill(); ctx.lineWidth = 2.5; ctx.strokeStyle = "rgba(255,255,255,.9)"; ctx.stroke();
    ctx.fillStyle = "#1b1620"; ctx.beginPath(); ctx.arc(x - r * .33, y - r * .2, r * .12, 0, 6.2832); ctx.arc(x + r * .33, y - r * .2, r * .12, 0, 6.2832); ctx.fill();
    ctx.strokeStyle = "#1b1620"; ctx.lineWidth = 1.4; ctx.beginPath(); ctx.arc(x, y - r * .02, r * .22, 0.15 * Math.PI, 0.85 * Math.PI); ctx.stroke();
    glyph(ctx, col, x, y + r * .5, r * .2, "rgba(255,255,255,.95)");
  }
  function frame(ts) {
    if (st.dead) return; st.raf = requestAnimationFrame(frame);
    const c = ctx; c.setTransform(sc, 0, 0, sc, 0, 0); c.clearRect(0, 0, CAP.W, CAP.H);
    const bg = c.createLinearGradient(0, 0, 0, CAP.H); bg.addColorStop(0, "#1a1622"); bg.addColorStop(1, "#2a2133"); c.fillStyle = bg; c.fillRect(0, 0, CAP.W, CAP.H);
    if (!st.tap) { c.fillStyle = "rgba(255,255,255,.045)"; c.fillRect(0, CAP.H / 2, CAP.W, CAP.H / 2); }          /* thumb zone */
    if (st.phase === "load" || st.phase === "err" || st.phase === "text") return;
    const t = performance.now() - st.t0, g = st.game, cf = st.cfg, k = st.sh.k;
    for (let i = 0; i < g.balls.length; i++) { const p = capBallPos(g, i, t, cf); ball(p[0], p[1], cf.size, capBallColor(g, i, t, cf)); }
    /* bullets in flight + hit effects */
    st.bul = st.bul.filter(b => { const el = t - b.t; if (el < 0) return true;
      const end = b.res.hit >= 0 ? b.res.t - b.t : 1000 * 340 / cf.bullet; if (el > end) { if (b.res.hit >= 0) st.fx.push({ t: t, ok: b.ok, p: capBallPos(g, b.res.hit, b.res.t, cf) }); return false; }
      const d = cf.bullet * el / 1000; c.beginPath(); c.arc(CAP.CX + Math.sin(b.ang) * d, CAP.CY - Math.cos(b.ang) * d, CAP.BR + 1, 0, 6.2832); c.fillStyle = "#fff"; c.fill(); return true; });
    st.fx = st.fx.filter(f => { const el = t - f.t; if (el > 500) return false; c.globalAlpha = 1 - el / 500; c.lineWidth = 3; c.strokeStyle = f.ok ? "#4ade80" : "#9ca3af";
      c.beginPath(); c.arc(f.p[0], f.p[1], cf.size + el / 12, 0, 6.2832); c.stroke(); c.fillStyle = c.strokeStyle; c.font = "bold 22px system-ui"; c.textAlign = "center"; c.fillText(f.ok ? "✓" : "✗", f.p[0], f.p[1] - cf.size - 8 - el / 25); c.globalAlpha = 1; return true; });
    if (st.tap) {      /* the question lives on the canvas only: a picture, not page text */
      const w = st.sh.target(), left = cf.max_shots - k;
      c.beginPath(); c.arc(34, 252, 17, 0, 6.2832); c.fillStyle = COLS[w].c; c.fill(); c.lineWidth = 3; c.strokeStyle = "#fff"; c.stroke(); glyph(c, w, 34, 252, 7, "#fff");
      c.textAlign = "left"; c.fillStyle = "#fff"; c.font = "700 19px system-ui"; c.fillText("Tap the " + COLS[w].n + " ball", 60, 259);
      c.textAlign = "center"; c.font = "600 14px system-ui"; c.fillStyle = "rgba(255,255,255,.75)";
      c.fillText(Array.from({ length: cf.hits }, (_, i) => i < st.sh.hits ? "●" : "○").join(" ") + "      tries left: " + left, CAP.CX, 284); return;
    }
    /* aim line: starts above the cannon and stays clear of the thumb (which is lower) */
    const want = st.sh.target(), aim = st.aim + (g.skews[Math.min(k, g.skews.length - 1)] || 0);
    if (st.sh.drag) { c.save(); c.setLineDash([6, 7]); c.lineWidth = 2.5; c.strokeStyle = "rgba(255,255,255,.75)"; c.beginPath();
      c.moveTo(CAP.CX + Math.sin(aim) * 44, CAP.CY - Math.cos(aim) * 44); c.lineTo(CAP.CX + Math.sin(aim) * 230, CAP.CY - Math.cos(aim) * 230); c.stroke(); c.restore();
      if (st.thumb) { c.beginPath(); c.arc(st.thumb[0], st.thumb[1] - 34, 11, 0, 6.2832); c.strokeStyle = "rgba(255,255,255,.35)"; c.lineWidth = 2; c.stroke(); } }
    /* cannon in the colour of the target */
    const ca = st.sh.drag ? aim : 0; c.save(); c.translate(CAP.CX, CAP.CY); c.rotate(ca); c.fillStyle = COLS[want].c; c.strokeStyle = "#fff"; c.lineWidth = 2.5;
    c.beginPath(); c.rect(-9, -38, 18, 40); c.fill(); c.stroke(); c.restore();
    c.beginPath(); c.arc(CAP.CX, CAP.CY + 6, 22, Math.PI, 0); c.fillStyle = "#3a3042"; c.fill(); c.strokeStyle = "#fff"; c.lineWidth = 2.5; c.stroke(); glyph(c, want, CAP.CX, CAP.CY - 4, 6, "#fff");
    if (st.hint && st.phase === "play") { c.fillStyle = "rgba(255,255,255," + (0.45 + 0.25 * Math.sin(ts / 300)) + ")"; c.font = "600 13px system-ui"; c.textAlign = "center"; c.fillText("thumb here  ·  slide  ·  let go", CAP.CX, 226); }
    if (performance.now() - st.flash < 300) { c.strokeStyle = "rgba(248,113,113,.8)"; c.lineWidth = 4; c.strokeRect(2, CAP.H / 2, CAP.W - 4, CAP.H / 2 - 2); }
  }
  st.raf = requestAnimationFrame(frame);
  start();
  return { stop() { st.dead = true; clearTimeout(st.autoT); cancelAnimationFrame(st.raf); if (ro) ro.disconnect(); }, restart() { clearTimeout(st.autoT); start(); }, state: st };
}
/* the site: a dimmed overlay with the card in the middle (half the screen).  -> Promise<{token, ttl} | null (closed)> */
let openModal = null;
function modal(o) {
  return new Promise(resolve => {
    addCss(); const ov = document.createElement("div"); ov.className = "capov"; const card = document.createElement("div"); card.className = "capcard"; ov.append(card);
    const prev = document.documentElement.style.overflow; document.documentElement.style.overflow = "hidden"; document.body.append(ov);
    let ctl = null, closed = false;
    const close = v => { if (closed) return; closed = true; if (openModal === close) openModal = null; if (ctl) ctl.stop(); ov.remove(); document.documentElement.style.overflow = prev; resolve(v); };
    openModal = close;
    ctl = run(card, Object.assign({}, o, { onPass: (tok, r) => setTimeout(() => close({ token: tok, ttl: r.ttl }), 650), onClose: () => close(null) }));
  });
}
const api = { ver: 11, modal, run, COLS, closeAll() { if (openModal) openModal(null); } };
root.CapGame = api;
const math = { CapTapper, CAP, capBallPos, capBallColor, capSimShot, capAim, CapShooter, capSha256, capPowOk, capSolvePow, capZeroBits };
root.CapMath = math;
if (typeof module !== "undefined") module.exports = math;
})(typeof window !== "undefined" ? window : globalThis);
