/* ==========================================================================
   Pipe Connect — a charity: water game
   --------------------------------------------------------------------------
   Rotate pipe tiles until water can flow from the yellow jerry-can source
   (left) to the village (right). 10 levels, no timer.

   Architecture:
     1. PUZZLE LOGIC   — pure functions: level generation, rotation math,
                         BFS flow / solvability checks. No DOM access.
     2. RENDERING      — builds the board DOM + SVG artwork from level data.
     3. GAME FLOW / UI — screens, HUD, water animation, modal, confetti.
   ========================================================================== */

'use strict';

/* ==========================================================================
   1. PUZZLE LOGIC (pure — no DOM)
   ========================================================================== */

/** Directions are indices: 0 = North, 1 = East, 2 = South, 3 = West. */
const N = 0, E = 1, S = 2, W = 3;
const DX = [0, 1, 0, -1];
const DY = [-1, 0, 1, 0];

/** Opposite of a direction (N<->S, E<->W). */
const opposite = (d) => (d + 2) % 4;

/**
 * Pipe piece catalogue.
 * `conns`  — which sides are open at rotation 0.
 * `d`      — SVG path drawing those arms in a 100x100 viewBox.
 * Rotating a piece by r quarter-turns clockwise maps side d -> (d + r) % 4,
 * which matches a CSS rotate(r * 90deg) of the artwork.
 */
const PIPE_SHAPES = {
  straight: { conns: [N, S],       d: 'M50 0 L50 100' },
  corner:   { conns: [N, E],       d: 'M50 0 L50 50 L100 50' },
  tee:      { conns: [N, E, S],    d: 'M50 0 L50 100 M50 50 L100 50' },
  cross:    { conns: [N, E, S, W], d: 'M50 0 L50 100 M0 50 L100 50' },
  dead:     { conns: [S],          d: 'M50 100 L50 55' },
};

const PIPE_NAMES = {
  straight: 'Straight', corner: 'Corner', tee: 'T-shaped',
  cross: 'Cross', dead: 'Dead-end',
};

/**
 * Level definitions. Each level is generated deterministically from its
 * seed, so "Reset" always restores the exact same puzzle.
 *   size        — grid is size x size
 *   meander     — 0..1, how much the solution path wanders (longer paths)
 *   upgrade     — chance a solution piece becomes a tee/cross (misleading extra openings)
 *   distractors — pool for non-solution tiles (repeats = heavier weighting)
 *   align       — force source and village onto the same row (level 1 tutorial)
 */
const LEVELS = [
  { size: 4, seed: 11,  meander: 0.10, upgrade: 0,    align: true, distractors: ['straight', 'straight', 'straight', 'corner'], hint: 'Mostly straight pipes — line them up across.' },
  { size: 4, seed: 23,  meander: 0.50, upgrade: 0,    distractors: ['corner', 'corner', 'straight'], hint: 'Corners ahead — follow the bends.' },
  { size: 5, seed: 36,  meander: 0.45, upgrade: 0.10, distractors: ['corner', 'straight', 'corner'], hint: 'A bigger grid. Trace the path before you turn.' },
  { size: 5, seed: 55,  meander: 0.55, upgrade: 0.20, distractors: ['corner', 'straight', 'tee', 'tee'], hint: 'Watch out — some pipes are only there to mislead.' },
  { size: 5, seed: 59,  meander: 0.80, upgrade: 0.20, distractors: ['corner', 'straight', 'tee'], hint: 'The path winds. Take your time — there is no clock.' },
  { size: 6, seed: 61,  meander: 0.55, upgrade: 0.25, distractors: ['corner', 'straight', 'tee'], hint: 'Six by six. Every village is worth it.' },
  { size: 6, seed: 101, meander: 0.65, upgrade: 0.25, distractors: ['corner', 'tee', 'dead', 'dead', 'straight'], hint: 'Dead ends look tempting — water needs a through-path.' },
  { size: 6, seed: 100, meander: 0.80, upgrade: 0.30, distractors: ['corner', 'tee', 'dead', 'straight'], hint: 'Lots of turns. Picture the flow before you click.' },
  { size: 6, seed: 106, meander: 0.85, upgrade: 0.35, distractors: ['corner', 'tee', 'dead', 'cross', 'straight'], hint: 'A real maze. You have got this.' },
  { size: 7, seed: 104, meander: 0.90, upgrade: 0.40, distractors: ['corner', 'tee', 'dead', 'cross'], hint: 'The final village. Make every connection count!' },
];

/** Deterministic pseudo-random generator (mulberry32). */
function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const randInt = (rng, n) => Math.floor(rng() * n);
const pick = (rng, arr) => arr[randInt(rng, arr.length)];

function shuffle(rng, arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = randInt(rng, i + 1);
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

/** Open sides of a cell at its current rotation. */
function cellConns(cell) {
  return PIPE_SHAPES[cell.type].conns.map((d) => (d + cell.rot) % 4);
}

/** All rotations of `type` whose open sides include every side in `sides`. */
function orientationsFor(type, sides) {
  const base = PIPE_SHAPES[type].conns;
  const out = [];
  for (let r = 0; r < 4; r++) {
    const conns = base.map((d) => (d + r) % 4);
    if (sides.every((s) => conns.includes(s))) out.push(r);
  }
  return out;
}

/**
 * Carve a random simple path from (0, srcRow) to (size-1, dstRow) using a
 * backtracking DFS. Low `meander` biases the walk eastward (short paths);
 * high `meander` lets it wander (long, twisty paths). Always succeeds.
 */
function carvePath(size, srcRow, dstRow, rng, meander) {
  const visited = new Set();
  const path = [];

  function dfs(x, y) {
    visited.add(y * size + x);
    path.push({ x, y });
    if (x === size - 1 && y === dstRow) return true;

    const dirs = shuffle(rng, [N, E, S, W].filter((d) => {
      const nx = x + DX[d], ny = y + DY[d];
      return nx >= 0 && ny >= 0 && nx < size && ny < size && !visited.has(ny * size + nx);
    }));
    // Bias: usually try East first so paths make steady progress.
    if (rng() > meander) {
      const i = dirs.indexOf(E);
      if (i > 0) { dirs.splice(i, 1); dirs.unshift(E); }
    }
    for (const d of dirs) {
      if (dfs(x + DX[d], y + DY[d])) return true;
    }
    visited.delete(y * size + x);
    path.pop();
    return false;
  }

  dfs(0, srcRow);
  return path;
}

/**
 * Flood-fill (BFS) from the source. Returns:
 *   depths       — Map of cellIndex -> BFS depth for every pipe water reaches
 *   solved       — true when water reaches the village inlet
 *   villageDepth — depth of the final cell (for animation timing)
 * Water flows between two adjacent cells only when BOTH have a matching
 * open side — this is the single source of truth for "connected".
 */
function computeFlow(level) {
  const { grid, size, srcRow, dstRow } = level;
  const depths = new Map();
  const result = { solved: false, depths, villageDepth: -1 };

  const startIdx = srcRow * size;                 // column 0
  if (!cellConns(grid[startIdx]).includes(W)) return result;  // must face the source

  depths.set(startIdx, 0);
  const queue = [startIdx];
  while (queue.length) {
    const idx = queue.shift();
    const x = idx % size, y = (idx - x) / size;
    for (const d of cellConns(grid[idx])) {
      const nx = x + DX[d], ny = y + DY[d];
      if (nx < 0 || ny < 0 || nx >= size || ny >= size) continue;
      const nIdx = ny * size + nx;
      if (depths.has(nIdx)) continue;
      if (!cellConns(grid[nIdx]).includes(opposite(d))) continue;
      depths.set(nIdx, depths.get(idx) + 1);
      queue.push(nIdx);
    }
  }

  const endIdx = dstRow * size + (size - 1);      // last column
  if (depths.has(endIdx) && cellConns(grid[endIdx]).includes(E)) {
    result.solved = true;
    result.villageDepth = depths.get(endIdx);
  }
  return result;
}

/**
 * Minimum number of clockwise clicks to restore every solution-path cell to
 * a working orientation. Used for the "perfect solution" bonus.
 */
function computePar(level) {
  let par = 0;
  for (const p of level.path) {
    const cell = level.grid[p.y * level.size + p.x];
    for (let k = 0; k < 4; k++) {
      const conns = PIPE_SHAPES[cell.type].conns.map((d) => (d + cell.rot + k) % 4);
      if (cell.need.every((s) => conns.includes(s))) { par += k; break; }
    }
  }
  return par;
}

/**
 * Build a complete, guaranteed-solvable level:
 *   1. carve a solution path source -> village
 *   2. lay exact-fit pipes along it (sometimes upgraded to tee/cross)
 *   3. fill the rest with distractor pipes
 *   4. scramble rotations, making sure the start position is unsolved
 */
function generateLevel(num) {
  const cfg = LEVELS[num - 1];
  const rng = mulberry32(cfg.seed);
  const size = cfg.size;

  const srcRow = randInt(rng, size);
  const dstRow = cfg.align ? srcRow : randInt(rng, size);
  const path = carvePath(size, srcRow, dstRow, rng, cfg.meander);
  const grid = new Array(size * size).fill(null);
  const level = { num, size, srcRow, dstRow, grid, path, par: 0 };

  // --- solution pipes ---
  for (let i = 0; i < path.length; i++) {
    const { x, y } = path[i];
    // Sides this cell must keep open: where water enters and where it leaves.
    const inSide = i === 0 ? W : opposite(dirBetween(path[i - 1], path[i]));
    const outSide = i === path.length - 1 ? E : dirBetween(path[i], path[i + 1]);
    const need = [inSide, outSide];

    let type = (inSide === opposite(outSide)) ? 'straight' : 'corner';
    if (rng() < cfg.upgrade) {
      const candidate = pick(rng, ['tee', 'cross']);
      if (orientationsFor(candidate, need).length) type = candidate;
    }
    const solRot = pick(rng, orientationsFor(type, need));
    grid[y * size + x] = { type, rot: solRot, need, onPath: true };
  }

  // --- distractor pipes everywhere else ---
  for (let i = 0; i < grid.length; i++) {
    if (!grid[i]) grid[i] = { type: pick(rng, cfg.distractors), rot: randInt(rng, 4), need: null, onPath: false };
  }

  // --- scramble the solution path ---
  for (const p of path) {
    const cell = grid[p.y * size + p.x];
    cell.rot = (cell.rot + randInt(rng, 4)) % 4;
  }

  // Keep scrambling until the puzzle is unsolved AND needs a fair number of
  // moves (so no level starts nearly finished).
  const minPar = Math.max(2, Math.round(path.length * 0.5));
  let guard = 0;
  while (guard++ < 300) {
    if (!computeFlow(level).solved && computePar(level) >= minPar) break;
    const p = path[randInt(rng, path.length)];
    const cell = grid[p.y * size + p.x];
    cell.rot = (cell.rot + 1 + randInt(rng, 3)) % 4;
  }
  // Absolute fallback: never hand the player an already-solved board.
  let fuse = 0;
  while (computeFlow(level).solved && fuse++ < 20) {
    for (const p of path) {
      const cell = grid[p.y * size + p.x];
      if (cell.type === 'cross') continue;   // rotating a cross changes nothing
      cell.rot = (cell.rot + 1) % 4;
      if (!computeFlow(level).solved) break;
    }
  }

  level.par = computePar(level);
  return level;
}

/** Direction of travel from path cell a to adjacent path cell b. */
function dirBetween(a, b) {
  if (b.x > a.x) return E;
  if (b.x < a.x) return W;
  return b.y > a.y ? S : N;
}

/* ==========================================================================
   2. RENDERING
   ========================================================================== */

/** SVG markup for one rotatable pipe tile. */
function buildPipeSVG(cell) {
  const shape = PIPE_SHAPES[cell.type];
  const hasJoint = cell.type !== 'straight';   // hub circle where arms meet
  return `
    <svg viewBox="0 0 100 100" aria-hidden="true" focusable="false">
      <path class="pipe-outer" d="${shape.d}"/>
      ${hasJoint ? '<circle class="joint-outer" cx="50" cy="50" r="17"/>' : ''}
      <path class="pipe-inner" d="${shape.d}"/>
      ${hasJoint ? '<circle class="joint-inner" cx="50" cy="50" r="11"/>' : ''}
      <path class="water" d="${shape.d}" pathLength="100"/>
      ${hasJoint ? '<circle class="water-joint" cx="50" cy="50" r="11"/>' : ''}
    </svg>`;
}

/** The water source: charity: water's iconic yellow jerry can. */
function buildSourceSVG() {
  return `
    <svg viewBox="0 0 100 100" aria-hidden="true" focusable="false">
      <path class="pipe-outer" d="M62 50 H100"/>
      <path class="pipe-inner" d="M62 50 H100"/>
      <path class="src-drop" d="M40 2 C40 2 33 11 33 15 a7 7 0 0 0 14 0 C47 11 40 2 40 2 Z" fill="#3FB6EA"/>
      <rect x="10" y="34" width="52" height="46" rx="8" fill="#FFC700" stroke="#E0AC00" stroke-width="3"/>
      <rect x="19" y="21" width="25" height="12" rx="6" fill="none" stroke="#E0AC00" stroke-width="5"/>
      <rect x="48" y="20" width="11" height="16" rx="2" fill="#FFC700" stroke="#E0AC00" stroke-width="3"/>
      <path d="M36 45 C36 45 28 55 28 60 a8 8 0 0 0 16 0 C44 55 36 45 36 45 Z" fill="#FFFFFF" opacity="0.92"/>
      <path class="water" d="M62 50 H100" pathLength="100"/>
    </svg>`;
}

/** The village: houses, tree and a tap that celebrate when water arrives. */
function buildVillageSVG() {
  return `
    <svg viewBox="0 0 100 100" aria-hidden="true" focusable="false">
      <rect x="6" y="78" width="88" height="7" rx="3.5" fill="#DEE8E3"/>
      <rect x="28" y="64" width="4" height="15" rx="2" fill="#9C7B54"/>
      <circle class="treetop" cx="30" cy="57" r="10"/>
      <rect x="38" y="52" width="26" height="26" rx="2" fill="#F4F7F8" stroke="#C9D6DD" stroke-width="2"/>
      <polygon points="35,53 51,38 67,53" fill="#00A19D"/>
      <rect class="win" x="46" y="59" width="10" height="10" rx="2"/>
      <rect x="70" y="60" width="20" height="18" rx="2" fill="#F4F7F8" stroke="#C9D6DD" stroke-width="2"/>
      <polygon points="67,61 80,49 93,61" fill="#FFC700"/>
      <rect class="win" x="76" y="65" width="8" height="8" rx="2"/>
      <path class="pipe-outer" d="M0 50 H22"/>
      <path class="pipe-inner" d="M0 50 H22"/>
      <rect x="17" y="46" width="9" height="34" rx="3" fill="#8FA3AE"/>
      <path class="droplet" d="M21.5 62 c0 0 -3.5 4.5 -3.5 7 a3.5 3.5 0 0 0 7 0 c0 -2.5 -3.5 -7 -3.5 -7 Z" fill="#3FB6EA"/>
      <path class="spark" d="M51 26 l2.5 5 5 2.5 -5 2.5 -2.5 5 -2.5 -5 -5 -2.5 5 -2.5 Z" fill="#FFC700"/>
      <path class="spark" d="M80 38 l2 4 4 2 -4 2 -2 4 -2 -4 -4 -2 4 -2 Z" fill="#3FB6EA"/>
      <path class="spark" d="M24 32 l2 4 4 2 -4 2 -2 4 -2 -4 -4 -2 4 -2 Z" fill="#00A19D"/>
      <path class="water" d="M0 50 H22" pathLength="100"/>
    </svg>`;
}

/**
 * Build the whole board for a level: source column | pipe grid | village
 * column, laid out on one CSS grid so everything stays aligned at any size.
 */
function renderBoard(level) {
  const { size, srcRow, dstRow, grid } = level;
  const board = els.board;
  board.innerHTML = '';
  board.classList.remove('locked');
  board.style.gridTemplateColumns = `repeat(${size + 2}, 1fr)`;
  board.style.gridTemplateRows = `repeat(${size}, 1fr)`;
  board.style.aspectRatio = `${size + 2} / ${size}`;
  // Cap width so tall boards still fit on screen above the fold.
  board.style.width = `min(100%, calc(72vh * ${(size + 2) / size}))`;

  state.cellEls = new Array(size * size);

  // Source (left) and village (right), aligned with the path's end rows.
  state.sourceEl = makeEndpoint('source', buildSourceSVG(), 1, srcRow + 1, 'Water source');
  state.villageEl = makeEndpoint('village', buildVillageSVG(), size + 2, dstRow + 1, 'Village');
  board.appendChild(state.sourceEl);

  // Pipe tiles are buttons: clickable, focusable, keyboard-operable.
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const idx = y * size + x;
      const cell = grid[idx];
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'cell';
      btn.dataset.idx = idx;
      btn.style.gridColumn = x + 2;
      btn.style.gridRow = y + 1;
      btn.setAttribute('aria-label',
        `${PIPE_NAMES[cell.type]} pipe, row ${y + 1}, column ${x + 1}. Activate to rotate.`);

      const rotor = document.createElement('div');
      rotor.className = 'rotor';
      rotor.style.transform = `rotate(${cell.rot * 90}deg)`;
      rotor.dataset.deg = cell.rot * 90;
      rotor.innerHTML = buildPipeSVG(cell);

      btn.appendChild(rotor);
      board.appendChild(btn);
      state.cellEls[idx] = btn;
    }
  }
  board.appendChild(state.villageEl);
}

function makeEndpoint(kind, svg, col, row, label) {
  const el = document.createElement('div');
  el.className = `endpoint ${kind}`;
  el.style.gridColumn = col;
  el.style.gridRow = row;
  el.setAttribute('role', 'img');
  el.setAttribute('aria-label', label);
  el.innerHTML = svg;
  return el;
}

/* ==========================================================================
   3. GAME FLOW / UI
   ========================================================================== */

/** Animation timing (ms). */
const ROTATE_MS = 300;       // matches the CSS rotor transition
const STAGGER_MS = 140;      // delay between pipes filling
const FILL_MS = 450;         // one pipe's fill duration (matches CSS)

/** Central mutable game state. */
const state = {
  levelNum: 1,
  level: null,     // generated level data (grid, path, par, ...)
  score: 0,
  moves: 0,
  locked: false,   // true while water flows / modal is up
  cellEls: [],
  sourceEl: null,
  villageEl: null,
  timers: [],      // pending timeouts, cleared on reset/home
};

/** Cached DOM references, filled in init(). */
const els = {};

function init() {
  const ids = ['board', 'hud-level', 'hud-moves', 'hud-score', 'hud-progress-text',
    'progress-fill', 'level-hint', 'modal-overlay', 'modal-points', 'modal-bonus',
    'btn-start', 'btn-reset', 'btn-home', 'btn-next', 'btn-play-again',
    'win-score', 'confetti'];
  for (const id of ids) {
    els[id.replace(/-([a-z])/g, (_, c) => c.toUpperCase())] = document.getElementById(id);
  }

  els.btnStart.addEventListener('click', startGame);
  els.btnReset.addEventListener('click', () => loadLevel(state.levelNum));
  els.btnHome.addEventListener('click', goHome);
  els.btnNext.addEventListener('click', nextLevel);
  els.btnPlayAgain.addEventListener('click', () => { clearConfetti(); startGame(); });

  // One delegated listener handles every pipe tile (click and keyboard).
  els.board.addEventListener('click', (e) => {
    const btn = e.target.closest('.cell');
    if (btn && !state.locked) rotateCell(Number(btn.dataset.idx));
  });
}

/** Begin a fresh game from level 1. */
function startGame() {
  state.score = 0;
  loadLevel(1);
  showScreen('game');
}

/** Generate, render and present level `num`. Also used by Reset. */
function loadLevel(num) {
  clearTimers();
  hideModal();
  state.levelNum = num;
  state.moves = 0;
  state.locked = false;
  state.level = generateLevel(num);
  renderBoard(state.level);
  els.levelHint.textContent = LEVELS[num - 1].hint;
  updateHUD();
}

/** Rotate one tile 90° clockwise, count the move, and re-check the flow. */
function rotateCell(idx) {
  const cell = state.level.grid[idx];
  cell.rot = (cell.rot + 1) % 4;

  // Always animate clockwise by accumulating degrees (never snap back).
  const rotor = state.cellEls[idx].querySelector('.rotor');
  const deg = Number(rotor.dataset.deg) + 90;
  rotor.dataset.deg = deg;
  rotor.style.transform = `rotate(${deg}deg)`;

  state.moves++;
  updateHUD();

  const flow = computeFlow(state.level);
  if (flow.solved) {
    state.locked = true;
    els.board.classList.add('locked');
    animateWater(flow);
  }
}

/**
 * The payoff: water flows from the source through every connected pipe,
 * one BFS layer at a time, then the village celebrates.
 */
function animateWater(flow) {
  const t0 = ROTATE_MS + 60;   // let the final rotation finish first

  schedule(t0, () => {
    state.sourceEl.classList.add('filled', 'flowing');
  });
  flow.depths.forEach((depth, idx) => {
    schedule(t0 + FILL_MS * 0.6 + depth * STAGGER_MS, () => {
      state.cellEls[idx].classList.add('filled');
    });
  });

  const villageTime = t0 + FILL_MS * 0.6 + (flow.villageDepth + 1) * STAGGER_MS;
  schedule(villageTime, () => state.villageEl.classList.add('filled'));
  schedule(villageTime + FILL_MS, () => state.villageEl.classList.add('celebrate'));
  schedule(villageTime + FILL_MS + 900, onLevelSolved);
}

/** Award points and show the "Level Complete!" modal. */
function onLevelSolved() {
  const perfect = state.moves <= state.level.par;
  state.score += 100 + (perfect ? 25 : 0);
  updateHUD();

  els.modalPoints.textContent = '100';
  els.modalBonus.hidden = !perfect;
  els.btnNext.textContent = state.levelNum >= LEVELS.length ? 'See Your Impact' : 'Next Level';
  els.modalOverlay.hidden = false;
  els.btnNext.focus();
}

/** Advance past the modal: next level, or the win screen after level 10. */
function nextLevel() {
  hideModal();
  if (state.levelNum >= LEVELS.length) {
    els.winScore.textContent = state.score;
    showScreen('win');
    launchConfetti();
  } else {
    loadLevel(state.levelNum + 1);
  }
}

function goHome() {
  clearTimers();
  hideModal();
  clearConfetti();
  showScreen('start');
}

/* ---------------- small UI helpers ---------------- */

function showScreen(name) {
  document.querySelectorAll('.screen').forEach((s) => s.classList.remove('active'));
  document.getElementById(`screen-${name}`).classList.add('active');
}

function updateHUD() {
  els.hudLevel.textContent = state.levelNum;
  els.hudMoves.textContent = state.moves;
  els.hudScore.textContent = state.score;
  els.hudProgressText.textContent = `Level ${state.levelNum} / ${LEVELS.length}`;
  els.progressFill.style.width = `${(state.levelNum / LEVELS.length) * 100}%`;
}

function hideModal() {
  els.modalOverlay.hidden = true;
}

function schedule(ms, fn) {
  state.timers.push(setTimeout(fn, ms));
}

function clearTimers() {
  state.timers.forEach(clearTimeout);
  state.timers = [];
}

/* ---------------- confetti ---------------- */

/** Fill the screen with falling brand-coloured confetti (win screen). */
function launchConfetti() {
  const colors = ['#FFC700', '#00A19D', '#3FB6EA', '#FFE066', '#7ADAD7', '#FFFFFF'];
  const frag = document.createDocumentFragment();
  for (let i = 0; i < 140; i++) {
    const piece = document.createElement('span');
    piece.className = 'confetti-piece';
    piece.style.left = `${Math.random() * 100}vw`;
    piece.style.background = colors[i % colors.length];
    piece.style.width = `${6 + Math.random() * 7}px`;
    piece.style.height = `${10 + Math.random() * 8}px`;
    piece.style.setProperty('--dur', `${2.6 + Math.random() * 2.4}s`);
    piece.style.setProperty('--delay', `${Math.random() * 1.4}s`);
    piece.style.setProperty('--spin', `${360 + Math.random() * 720}deg`);
    frag.appendChild(piece);
  }
  els.confetti.appendChild(frag);
  schedule(7500, clearConfetti);
}

function clearConfetti() {
  els.confetti.innerHTML = '';
}

/* ---------------- boot ---------------- */

document.addEventListener('DOMContentLoaded', init);

/**
 * Dev/test hooks — lets the console (and automated tests) exercise the pure
 * puzzle logic. Not used by the game itself.
 */
window.PipeConnect = {
  state, LEVELS, PIPE_SHAPES,
  generateLevel, computeFlow, computePar, cellConns, orientationsFor,
  loadLevel, startGame,
};
