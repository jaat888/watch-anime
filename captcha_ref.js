// captcha_ref.js - the page's copy of the game maths (Step 8 pastes this into index.html).
// It must give the SAME answers as captcha.py (ball_pos / ball_color / sim_shot).  test_step7.py
// runs both on the same games and compares them (needs node; skipped when node is missing).
// game = what /api/captcha/new sent: {type, balls[], targets[], skews[]};  cfg = its "cfg";  W=360, H=300
const CAP = { W: 360, H: 300, CX: 180, CY: 284, BR: 5, STEP: 8, NCOL: 4 };
function capTri(x) { const f = x - Math.floor(x); return 4 * Math.abs(f - 0.5) - 1; }
function capBallPos(game, i, tMs, cfg) {
  const p = game.balls[i], T = 2 * Math.PI; let u = tMs / 1000 * cfg.speed; if (game.type !== 1) u *= (p.dir || 1);
  if (game.type === 0) return [180 + 118 * capTri(u * p.f + p.ph / T), p.y + 20 * Math.sin(u * p.g + p.ph2)];
  if (game.type === 1) { const a = u * p.f * p.dir + p.ph; return [180 + p.rx * Math.cos(a), 110 + p.ry * Math.sin(a)]; }
  if (game.type === 2) return [180 + 125 * Math.sin(u * p.f + p.ph), 105 + 55 * Math.sin(u * p.g + p.ph2)];
  const a = u * p.f + p.ph; return [180 + 122 * Math.sin(a), 105 + p.ry * Math.sin(2 * a + p.ph2)];
}
function capBallColor(game, i, tMs, cfg) { return game.balls[i].c % CAP.NCOL; }
// k = shot number, tMs = fire time, a = finger angle.  The bullet flies along a + skew[k].
function capSimShot(game, cfg, k, tMs, a) {
  const ang = a + game.skews[k], dx = Math.sin(ang), dy = -Math.cos(ang), vb = cfg.bullet, reach = cfg.size + CAP.BR + (cfg.slack === undefined ? 3 : cfg.slack);
  let ms = Math.round(tMs); const end = ms + Math.trunc(1000 * 340 / vb);
  while (ms <= end) {
    const d = vb * (ms - tMs) / 1000, bx = CAP.CX + dx * d, by = CAP.CY + dy * d;
    if (bx < -CAP.BR || bx > CAP.W + CAP.BR || by < -CAP.BR) break;
    let best = -1, bd = 1e18;
    for (let i = 0; i < game.balls.length; i++) {
      const [x, y] = capBallPos(game, i, ms, cfg), dd = (x - bx) ** 2 + (y - by) ** 2;
      if (dd <= reach * reach && dd < bd) { best = i; bd = dd; }
    }
    if (best >= 0) return { hit: best, t: ms, color: capBallColor(game, best, ms, cfg) };
    ms += CAP.STEP;
  }
  return { hit: -1, t: null, color: null };
}
if (typeof module !== 'undefined') module.exports = { capBallPos, capBallColor, capSimShot, CAP };
