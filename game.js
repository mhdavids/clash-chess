'use strict';
/* Clash Chess — chess where every capture is a duel either side can win. */

// hp = hit points, dmg = damage per hit, zone = hit-zone width on the strike meter (0..1)
const STATS = {
  p: { name: 'Pawn',   hp: 3, dmg: 1, zone: 0.22, val: 1 },
  n: { name: 'Knight', hp: 5, dmg: 2, zone: 0.30, val: 3 },
  b: { name: 'Bishop', hp: 5, dmg: 2, zone: 0.30, val: 3 },
  r: { name: 'Rook',   hp: 6, dmg: 2, zone: 0.34, val: 5 },
  q: { name: 'Queen',  hp: 8, dmg: 3, zone: 0.40, val: 9 },
  k: { name: 'King',   hp: 6, dmg: 2, zone: 0.34, val: 200 },
};
const VS = '︎'; // force text (not emoji) rendering on iOS
const GLYPH = { k: '♚' + VS, q: '♛' + VS, r: '♜' + VS, b: '♝' + VS, n: '♞' + VS, p: '♟' + VS };
const CRIT = 0.3;        // central fraction of the hit zone that deals double damage
const AI_NOISE = 0.13;   // std-dev of the computer's aim, as a fraction of the meter
const COLOR = { w: 'White', b: 'Black' };

const $ = (id) => document.getElementById(id);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const sqName = (i) => 'abcdefgh'[i & 7] + (8 - (i >> 3));
const other = (c) => (c === 'w' ? 'b' : 'w');

let board, turn, ep, sel, legal, lastMove, over, busy, gameId = 0;
let mode = 'ai';

/* ---------------- rules ---------------- */

function newBoard() {
  const b = Array(64).fill(null);
  const back = ['r', 'n', 'b', 'q', 'k', 'b', 'n', 'r'];
  const mk = (t, c) => ({ t, c, hp: STATS[t].hp, moved: false });
  for (let f = 0; f < 8; f++) {
    b[f] = mk(back[f], 'b'); b[8 + f] = mk('p', 'b');
    b[48 + f] = mk('p', 'w'); b[56 + f] = mk(back[f], 'w');
  }
  return b;
}

const KN = [[-2, -1], [-2, 1], [-1, -2], [-1, 2], [1, -2], [1, 2], [2, -1], [2, 1]];
const DIAG = [[-1, -1], [-1, 1], [1, -1], [1, 1]];
const ORTH = [[-1, 0], [1, 0], [0, -1], [0, 1]];

// Pseudo-legal moves (there is no check in this variant — kings are fought, not mated).
function genMoves(b, c, epSq) {
  const out = [];
  const add = (from, to, extra) => out.push(Object.assign({ from, to, capture: false, victim: to }, extra));
  for (let i = 0; i < 64; i++) {
    const p = b[i];
    if (!p || p.c !== c) continue;
    const r = i >> 3, f = i & 7;
    const step = (dirs, slide) => {
      for (const [dr, df] of dirs) {
        let rr = r + dr, ff = f + df;
        while (rr >= 0 && rr < 8 && ff >= 0 && ff < 8) {
          const j = rr * 8 + ff, q = b[j];
          if (!q) add(i, j);
          else { if (q.c !== c) add(i, j, { capture: true }); break; }
          if (!slide) break;
          rr += dr; ff += df;
        }
      }
    };
    if (p.t === 'p') {
      const d = c === 'w' ? -1 : 1, r1 = r + d;
      if (r1 < 0 || r1 > 7) continue;
      if (!b[r1 * 8 + f]) {
        add(i, r1 * 8 + f);
        const start = c === 'w' ? 6 : 1;
        if (r === start && !b[(r + 2 * d) * 8 + f]) add(i, (r + 2 * d) * 8 + f, { double: true });
      }
      for (const df of [-1, 1]) {
        const ff = f + df;
        if (ff < 0 || ff > 7) continue;
        const j = r1 * 8 + ff;
        if (b[j] && b[j].c !== c) add(i, j, { capture: true });
        else if (j === epSq && b[r * 8 + ff] && b[r * 8 + ff].c !== c)
          add(i, j, { capture: true, ep: true, victim: r * 8 + ff });
      }
    } else if (p.t === 'n') step(KN, false);
    else if (p.t === 'b') step(DIAG, true);
    else if (p.t === 'r') step(ORTH, true);
    else if (p.t === 'q') step(DIAG.concat(ORTH), true);
    else {
      step(DIAG.concat(ORTH), false);
      if (!p.moved && f === 4) {
        const row = r * 8, rk = b[row + 7], rq = b[row];
        if (rk && rk.t === 'r' && rk.c === c && !rk.moved && !b[row + 5] && !b[row + 6]) add(i, row + 6, { castle: 'k' });
        if (rq && rq.t === 'r' && rq.c === c && !rq.moved && !b[row + 1] && !b[row + 2] && !b[row + 3]) add(i, row + 2, { castle: 'q' });
      }
    }
  }
  return out;
}

// Put the mover on its destination (assumes any battle was won). Returns the new en-passant square.
function place(b, m) {
  const p = b[m.from];
  b[m.from] = null;
  if (m.ep) b[m.victim] = null;
  b[m.to] = p;
  p.moved = true;
  if (m.castle) {
    const row = m.to - (m.to & 7);
    const [rf, rt] = m.castle === 'k' ? [row + 7, row + 5] : [row, row + 3];
    b[rt] = b[rf]; b[rf] = null; b[rt].moved = true;
  }
  const r = m.to >> 3;
  if (p.t === 'p' && (r === 0 || r === 7)) { p.t = 'q'; p.hp = STATS.q.hp; }
  return m.double ? (m.from + m.to) / 2 : -1;
}

/* ---------------- battle maths ---------------- */

function gauss() {
  let u = 0;
  while (!u) u = Math.random();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * Math.random());
}
// Damage for a strike that lands `dist` away from the zone centre.
function strikeDamage(t, dist) {
  const half = STATS[t].zone / 2;
  if (dist <= half * CRIT) return { dmg: STATS[t].dmg * 2, kind: 'crit' };
  if (dist <= half) return { dmg: STATS[t].dmg, kind: 'dmg' };
  return { dmg: 0, kind: 'miss' };
}
// Estimated chance the attacker wins, assuming both sides aim like the computer does.
const probCache = new Map();
function winProb(att, def) {
  const key = att.t + att.hp + def.t + def.hp;
  if (probCache.has(key)) return probCache.get(key);
  const N = 400;
  let wins = 0;
  for (let n = 0; n < N; n++) {
    let a = att.hp, d = def.hp;
    for (;;) {
      d -= strikeDamage(att.t, Math.abs(gauss() * AI_NOISE)).dmg;
      if (d <= 0) { wins++; break; }
      a -= strikeDamage(def.t, Math.abs(gauss() * AI_NOISE)).dmg;
      if (a <= 0) break;
    }
  }
  probCache.set(key, wins / N);
  return wins / N;
}

/* ---------------- battle screen ---------------- */

let strikeNow = null; // set while a human may strike

function pips(el, p) {
  const max = STATS[p.t].hp;
  el.innerHTML = '';
  for (let i = 0; i < max; i++) {
    const s = document.createElement('i');
    if (i >= p.hp) s.className = 'x';
    el.appendChild(s);
  }
}
function setFighter(el, p) {
  const g = el.querySelector('.glyph');
  g.textContent = GLYPH[p.t];
  g.className = 'glyph ' + p.c;
  el.querySelector('.fname').textContent = `${COLOR[p.c]} ${STATS[p.t].name}`;
  el.classList.remove('dead', 'active');
  pips(el.querySelector('.pips'), p);
}
function retrigger(el, cls) {
  el.classList.remove(cls);
  void el.offsetWidth;
  el.classList.add(cls);
}
function isHuman(c) {
  if ($('auto').checked) return false;
  return mode === '2p' || c === 'w';
}

// Run the meter for one strike; resolves with {dmg, kind}.
function strike(p, human, round) {
  return new Promise((resolve) => {
    const w = STATS[p.t].zone;
    const centre = w / 2 + 0.04 + Math.random() * (1 - w - 0.08);
    $('zone').style.left = (centre - w / 2) * 100 + '%';
    $('zone').style.width = w * 100 + '%';
    const sweep = Math.max(430, 640 - round * 18); // ms per pass; duels speed up
    const phase = Math.random() * 2;
    const quick = $('auto').checked;
    const target = Math.min(1, Math.max(0, centre + gauss() * AI_NOISE));
    const t0 = performance.now();
    let pos = 0, done = false, raf;
    const btn = $('strike');
    btn.disabled = true;

    const finish = () => {
      if (done) return;
      done = true;
      cancelAnimationFrame(raf);
      strikeNow = null;
      btn.disabled = true;
      resolve(strikeDamage(p.t, Math.abs(pos - centre)));
    };
    const frame = (now) => {
      const t = now - t0;
      const x = (t / sweep + phase) % 2;
      pos = x < 1 ? x : 2 - x;
      $('marker').style.left = pos * 100 + '%';
      if (!human) {
        const minT = quick ? 120 : 520;
        if ((t > minT && Math.abs(pos - target) < 0.04) || t > 3000) { pos = t > 3000 ? target : pos; return finish(); }
      }
      raf = requestAnimationFrame(frame);
    };
    raf = requestAnimationFrame(frame);
    if (human) setTimeout(() => { if (!done) { btn.disabled = false; strikeNow = finish; } }, 220);
  });
}

async function battle(att, def) {
  const fa = $('fa'), fd = $('fd');
  setFighter(fa, att); setFighter(fd, def);
  $('btitle').textContent = `⚔ ${COLOR[att.c]} ${STATS[att.t].name} attacks ${COLOR[def.c]} ${STATS[def.t].name}`;
  $('prompt').className = '';
  $('prompt').textContent = '';
  $('battle').hidden = false;
  const quick = $('auto').checked;
  await sleep(quick ? 250 : 600);

  let s = att, t = def, round = 0;
  while (att.hp > 0 && def.hp > 0) {
    const sEl = s === att ? fa : fd, tEl = s === att ? fd : fa;
    const human = isHuman(s.c);
    sEl.classList.add('active'); tEl.classList.remove('active');
    $('prompt').textContent = human
      ? `${COLOR[s.c]} ${STATS[s.t].name}: hit STRIKE (or Space) in the green!`
      : `${COLOR[s.c]} ${STATS[s.t].name} winds up…`;
    const res = await strike(s, human, round);
    retrigger(sEl.querySelector('.glyph'), s === att ? 'lungeR' : 'lungeL');
    const fl = tEl.querySelector('.float');
    fl.className = 'float ' + res.kind;
    fl.textContent = res.kind === 'miss' ? 'MISS' : (res.kind === 'crit' ? 'CRIT −' : '−') + res.dmg;
    retrigger(fl, 'go');
    if (res.dmg) {
      t.hp = Math.max(0, t.hp - res.dmg);
      retrigger(tEl.querySelector('.glyph'), 'shake');
      pips(tEl.querySelector('.pips'), t);
    }
    await sleep(quick ? 380 : 750);
    [s, t] = [t, s];
    round++;
  }
  const attWon = def.hp <= 0;
  const winner = attWon ? att : def;
  (attWon ? fd : fa).classList.add('dead');
  fa.classList.remove('active'); fd.classList.remove('active');
  $('prompt').className = 'big';
  $('prompt').textContent = attWon
    ? `${COLOR[winner.c]} ${STATS[winner.t].name} takes the square!`
    : `${COLOR[winner.c]} ${STATS[winner.t].name} holds the square!`;
  await sleep(quick ? 800 : 1400);
  $('battle').hidden = true;
  return attWon;
}

/* ---------------- game flow ---------------- */

function log(text, fight) {
  const li = document.createElement('li');
  li.textContent = text;
  if (fight) li.className = 'fight';
  $('log').prepend(li);
}

async function playMove(m) {
  const id = gameId;
  busy = true; sel = null; legal = [];
  const att = board[m.from];
  const def = m.capture ? board[m.victim] : null;
  const attName = `${COLOR[att.c]} ${STATS[att.t].name}`;
  lastMove = [m.from, m.to];
  render();

  let attWon = true;
  if (def) {
    const defName = `${COLOR[def.c]} ${STATS[def.t].name}`;
    attWon = await battle(att, def);
    if (id !== gameId) return;
    log(attWon
      ? `⚔ ${attName} beat ${defName} on ${sqName(m.victim)} (${att.hp} HP left)`
      : `🛡 ${defName} on ${sqName(m.victim)} repelled ${attName} (${def.hp} HP left)`, true);
  }
  if (attWon) {
    const wasPawn = att.t === 'p';
    ep = place(board, m);
    if (!def) log(m.castle ? `${COLOR[att.c]} castles` : `${attName} ${sqName(m.from)}→${sqName(m.to)}`);
    if (wasPawn && att.t === 'q') log(`${COLOR[att.c]} pawn promotes to a Queen on ${sqName(m.to)}`, true);
  } else {
    board[m.from] = null;
    ep = -1;
  }

  const fallen = def && attWon ? def : (!attWon ? att : null);
  if (fallen && fallen.t === 'k') over = `${COLOR[other(fallen.c)]} wins — the ${COLOR[fallen.c]} King has fallen!`;
  turn = other(turn);
  if (!over && !genMoves(board, turn, ep).length) over = 'Draw — no moves available.';
  if (over) log(over, true);
  busy = false;
  render();
  if (!over && mode === 'ai' && turn === 'b') setTimeout(() => { if (id === gameId) aiMove(); }, 550);
}

/* ---------------- computer opponent ---------------- */

const worth = (p) => STATS[p.t].val * (0.4 + 0.6 * p.hp / STATS[p.t].hp);
const centrality = (i) => 3.5 - Math.max(Math.abs((i >> 3) - 3.5), Math.abs((i & 7) - 3.5));

function aiMove() {
  const me = turn, moves = genMoves(board, me, ep);
  let best = null, bestScore = -Infinity;
  for (const m of moves) {
    const a = board[m.from];
    let score = Math.random() * 0.25, p = 1;
    if (m.capture) {
      const d = board[m.victim];
      p = winProb(a, d);
      score += p * worth(d) - (1 - p) * worth(a);
    }
    if (a.t === 'p') score += 0.06;
    else if (a.t === 'k') score -= 0.25;
    else score += 0.1 * (centrality(m.to) - centrality(m.from));
    if (m.castle) score += 0.6;
    // What is the opponent's best battle after this move?
    const nb = board.map((x) => x && Object.assign({}, x));
    const nep = place(nb, m);
    if (a.t === 'p' && nb[m.to].t === 'q') score += 6;
    let threat = 0;
    for (const om of genMoves(nb, other(me), nep)) {
      if (!om.capture) continue;
      const oa = nb[om.from], od = nb[om.victim], q = winProb(oa, od);
      threat = Math.max(threat, q * worth(od) - (1 - q) * worth(oa));
    }
    score -= 0.85 * p * threat;
    if (score > bestScore) { bestScore = score; best = m; }
  }
  if (best) playMove(best);
}

/* ---------------- board UI ---------------- */

function render() {
  const el = $('board');
  el.innerHTML = '';
  const targets = new Map(legal.map((m) => [m.to, m]));
  for (let i = 0; i < 64; i++) {
    const d = document.createElement('div');
    d.className = 'sq ' + (((i >> 3) + (i & 7)) % 2 ? 'd' : 'l');
    d.dataset.i = i;
    if (lastMove && lastMove.includes(i)) d.classList.add('last');
    if (i === sel) d.classList.add('sel');
    if (targets.has(i)) d.classList.add(targets.get(i).capture ? 'cap' : 'move');
    const p = board[i];
    if (p) {
      const s = document.createElement('span');
      s.className = 'pc ' + p.c;
      s.textContent = GLYPH[p.t];
      d.appendChild(s);
      const max = STATS[p.t].hp;
      if (p.hp < max) {
        const bar = document.createElement('div');
        bar.className = 'hpbar';
        bar.title = `${p.hp}/${max} HP`;
        for (let k = 0; k < max; k++) { const b = document.createElement('i'); if (k >= p.hp) b.className = 'x'; bar.appendChild(b); }
        d.appendChild(bar);
      }
    }
    el.appendChild(d);
  }
  const st = $('status');
  st.className = over ? 'over' : '';
  st.textContent = over || (mode === 'ai'
    ? (turn === 'w' ? 'Your move (White)' : 'Computer is thinking…')
    : `${COLOR[turn]} to move`);
}

function onSquare(i) {
  if (busy || over || (mode === 'ai' && turn === 'b')) return;
  const m = legal.find((x) => x.to === i);
  if (m) return playMove(m);
  const p = board[i];
  if (p && p.c === turn && i !== sel) {
    sel = i;
    legal = genMoves(board, turn, ep).filter((x) => x.from === i);
  } else { sel = null; legal = []; }
  render();
}

function newGame() {
  gameId++;
  board = newBoard(); turn = 'w'; ep = -1; sel = null; legal = []; lastMove = null; over = ''; busy = false;
  mode = $('mode').value;
  $('log').innerHTML = '';
  $('battle').hidden = true;
  render();
}

function init() {
  const rows = ['<tr><th></th><th>Piece</th><th>HP</th><th>Damage</th><th>Aim</th></tr>'];
  for (const t of ['p', 'n', 'b', 'r', 'q', 'k']) {
    const s = STATS[t];
    rows.push(`<tr><td>${GLYPH[t]}</td><td>${s.name}</td><td>${s.hp}</td><td>${s.dmg}</td><td>${Math.round(s.zone * 100)}%</td></tr>`);
  }
  $('stats').innerHTML = rows.join('');
  $('board').addEventListener('click', (e) => {
    const sq = e.target.closest('.sq');
    if (sq) onSquare(+sq.dataset.i);
  });
  $('new').addEventListener('click', newGame);
  $('mode').addEventListener('change', newGame);
  $('strike').addEventListener('click', () => { if (strikeNow) strikeNow(); });
  document.addEventListener('keydown', (e) => {
    if ((e.code === 'Space' || e.code === 'Enter') && !$('battle').hidden) {
      e.preventDefault();
      if (strikeNow && !e.repeat) strikeNow();
    }
  });
  newGame();
}
init();
