import { haptic } from 'ios-haptics';

// ---------- Palette ----------
const PALETTE = [
  '#FF69B4', // pink
  '#5ec8ff', // blue
  '#5ee08c', // green
  '#ffd166', // yellow
  '#ff5b6e', // red
  '#c38bff', // purple
  '#ff9b5e', // orange
  '#7aeaea', // teal
];

// ---------- State ----------
let level = 1;
let rows = 4, cols = 4, numColors = 2;
let grid = [];      // [r][c] = colorIndex or -1
let tileIds = [];   // [r][c] = tileId or -1 (parallel to grid)
let tiles = new Map(); // tileId -> { el, r, c }
let nextTileId = 1;
let cellSize = 40;
let score = 0;
let moves = 0;
let hoverGroup = new Set();
let gameOver = false;
let busy = false;

const STARTING_POWER_UPS = { rotateCW: 0, rotateCCW: 0, clearRow: 0, clearCol: 0, bomb: 0, undo: 0, hint: 3 };
let powerUps = { ...STARTING_POWER_UPS };
let activePowerUp = null;

const POWER_UP_ICONS = {
  rotateCW: 'hgi-rotate-clockwise',
  rotateCCW: 'hgi-rotate-02',
  clearRow: 'hgi-arrow-horizontal',
  clearCol: 'hgi-arrow-vertical',
  bomb: 'hgi-bomb',
  undo: 'hgi-arrow-turn-backward',
  hint: 'hgi-idea-01',
};
const POWER_UP_KEYS = Object.keys(POWER_UP_ICONS);
const POWER_UP_TILE_TTL = 4;
let tilePowerUps = new Map(); // tileId -> { key, remaining }

const UNDO_STACK_MAX = 50;
let undoStack = [];
let pendingLevelTimeout = null;

const GAP_X = 7;
const GAP_Y = 11;
const PADDING = 6;
const SHADOW_DEPTH = 5;
const FADE_MS = 180;
const SLIDE_MS = 280;

function darken(hex, pct) {
  const h = hex.replace('#', '');
  const r = parseInt(h.slice(0, 2), 16);
  const g = parseInt(h.slice(2, 4), 16);
  const b = parseInt(h.slice(4, 6), 16);
  const mul = 1 - pct;
  const toHex = (n) => Math.max(0, Math.min(255, Math.round(n * mul))).toString(16).padStart(2, '0');
  return '#' + toHex(r) + toHex(g) + toHex(b);
}

const SHADOW_PALETTE = PALETTE.map((c) => darken(c, 0.35));

const boardEl = document.getElementById('board');
const boardWrapEl = document.querySelector('.board-wrap');
const scoreEl = document.getElementById('score');
const remainingEl = document.getElementById('remaining');
const movesEl = document.getElementById('moves');
const levelEl = document.getElementById('level');

// ---------- Level curve ----------
// Grid stays at 10x10; difficulty ramps via number of colors.
function levelConfig(lvl) {
  const size = Math.min(12, 6 + 2 * Math.floor((lvl - 1) / 4));
  const colorSteps = [2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 6, 6];
  const colors = colorSteps[Math.min(lvl - 1, colorSteps.length - 1)] ?? PALETTE.length;
  return { rows: size, cols: size, colors: Math.min(PALETTE.length, colors) };
}

// ---------- Grid helpers ----------
function cloneGrid(g) { return g.map(row => row.slice()); }

function findGroup(g, r, c) {
  const color = g[r][c];
  if (color < 0) return [];
  const R = g.length, C = g[0].length;
  const seen = new Set();
  const stack = [[r, c]];
  const group = [];
  while (stack.length) {
    const [cr, cc] = stack.pop();
    const key = cr * C + cc;
    if (seen.has(key)) continue;
    if (cr < 0 || cc < 0 || cr >= R || cc >= C) continue;
    if (g[cr][cc] !== color) continue;
    seen.add(key);
    group.push([cr, cc]);
    stack.push([cr + 1, cc], [cr - 1, cc], [cr, cc + 1], [cr, cc - 1]);
  }
  return group;
}

function applyGravity(g, tg) {
  const R = g.length, C = g[0].length;
  for (let c = 0; c < C; c++) {
    let write = R - 1;
    for (let r = R - 1; r >= 0; r--) {
      if (g[r][c] !== -1) {
        const v = g[r][c];
        const tid = tg ? tg[r][c] : -1;
        g[r][c] = -1;
        g[write][c] = v;
        if (tg) { tg[r][c] = -1; tg[write][c] = tid; }
        write--;
      }
    }
  }
  // Horizontal compaction: shift non-empty columns to the left so empty
  // columns don't leave gaps in the middle of the board.
  let writeCol = 0;
  for (let c = 0; c < C; c++) {
    let colEmpty = true;
    for (let r = 0; r < R; r++) if (g[r][c] !== -1) { colEmpty = false; break; }
    if (!colEmpty) {
      if (writeCol !== c) {
        for (let r = 0; r < R; r++) {
          g[r][writeCol] = g[r][c];
          g[r][c] = -1;
          if (tg) { tg[r][writeCol] = tg[r][c]; tg[r][c] = -1; }
        }
      }
      writeCol++;
    }
  }
}

function findAllGroups(g) {
  const R = g.length, C = g[0].length;
  const visited = Array.from({ length: R }, () => new Array(C).fill(false));
  const groups = [];
  for (let r = 0; r < R; r++) {
    for (let c = 0; c < C; c++) {
      if (visited[r][c] || g[r][c] < 0) continue;
      const group = findGroup(g, r, c);
      group.forEach(([gr, gc]) => (visited[gr][gc] = true));
      if (group.length >= 2) groups.push(group);
    }
  }
  return groups;
}

function isEmpty(g) {
  for (let r = 0; r < g.length; r++)
    for (let c = 0; c < g[0].length; c++)
      if (g[r][c] !== -1) return false;
  return true;
}

function countRemaining(g) {
  let n = 0;
  for (let r = 0; r < g.length; r++)
    for (let c = 0; c < g[0].length; c++)
      if (g[r][c] !== -1) n++;
  return n;
}

function gridKey(g) {
  return g.map(row => row.join(',')).join('|');
}

// ---------- Solver (checks if fully clearable) ----------
function isSolvable(startGrid, budget = 20000) {
  const memo = new Set();
  let steps = 0;

  function dfs(g) {
    if (steps++ > budget) return null; // unknown
    if (isEmpty(g)) return true;
    const key = gridKey(g);
    if (memo.has(key)) return false;
    memo.add(key);

    const groups = findAllGroups(g);
    if (groups.length === 0) return false;

    groups.sort((a, b) => b.length - a.length);

    for (const group of groups) {
      const ng = cloneGrid(g);
      for (const [r, c] of group) ng[r][c] = -1;
      applyGravity(ng);
      const res = dfs(ng);
      if (res === true) return true;
      if (res === null) return null;
    }
    return false;
  }

  return dfs(startGrid);
}

// ---------- Generation ----------
function randomGrid(R, C, K) {
  const g = Array.from({ length: R }, () => new Array(C));
  for (let r = 0; r < R; r++)
    for (let c = 0; c < C; c++)
      g[r][c] = Math.floor(Math.random() * K);
  return g;
}

function fragmentedGrid(R, C, K, matchChance = 0.35) {
  const g = Array.from({ length: R }, () => new Array(C).fill(-1));
  for (let r = 0; r < R; r++) {
    for (let c = 0; c < C; c++) {
      if (Math.random() < matchChance) {
        g[r][c] = Math.floor(Math.random() * K);
        continue;
      }
      const banned = new Set();
      if (r > 0) banned.add(g[r - 1][c]);
      if (c > 0) banned.add(g[r][c - 1]);
      const choices = [];
      for (let k = 0; k < K; k++) if (!banned.has(k)) choices.push(k);
      const pool = choices.length ? choices : Array.from({ length: K }, (_, i) => i);
      g[r][c] = pool[Math.floor(Math.random() * pool.length)];
    }
  }
  const counts = new Array(K).fill(0);
  for (let r = 0; r < R; r++) for (let c = 0; c < C; c++) counts[g[r][c]]++;
  const odd = [];
  for (let k = 0; k < K; k++) if (counts[k] % 2 === 1) odd.push(k);
  for (let i = 0; i + 1 < odd.length; i += 2) {
    outer: for (let r = 0; r < R; r++) {
      for (let c = 0; c < C; c++) {
        if (g[r][c] === odd[i]) { g[r][c] = odd[i + 1]; counts[odd[i]]--; counts[odd[i + 1]]++; break outer; }
      }
    }
  }
  return g;
}

function generateSolvable(R, C, K, matchChance = 0.35) {
  for (let attempt = 0; attempt < 12; attempt++) {
    const g = fragmentedGrid(R, C, K, matchChance);
    const res = isSolvable(cloneGrid(g), 15000);
    if (res === true) return g;
  }
  for (let attempt = 0; attempt < 8; attempt++) {
    const g = randomGrid(R, C, K);
    const res = isSolvable(cloneGrid(g), 15000);
    if (res === true) return g;
  }
  return constructSolvable(R, C, K);
}

function constructSolvable(R, C, K) {
  const total = R * C;
  const counts = new Array(K).fill(0);
  let remaining = total;
  for (let i = 0; i < K; i++) { counts[i] = 2; remaining -= 2; }
  while (remaining > 0) {
    const k = Math.floor(Math.random() * K);
    const add = Math.min(2, remaining);
    counts[k] += add;
    remaining -= add;
  }

  const bag = [];
  for (let k = 0; k < K; k++) for (let i = 0; i < counts[k]; i++) bag.push(k);
  for (let i = bag.length - 1; i > 0; i--) {
    const j = Math.max(0, i - 3 - Math.floor(Math.random() * 4));
    const swap = j + Math.floor(Math.random() * (i - j + 1));
    [bag[i], bag[swap]] = [bag[swap], bag[i]];
  }

  const g = Array.from({ length: R }, () => new Array(C).fill(-1));
  let idx = 0;
  for (let c = 0; c < C; c++) {
    for (let r = R - 1; r >= 0; r--) {
      g[r][c] = bag[idx++];
    }
  }

  const res = isSolvable(cloneGrid(g), 30000);
  if (res === true) return g;

  for (let attempt = 0; attempt < 20; attempt++) {
    const rg = randomGrid(R, C, K);
    if (isSolvable(cloneGrid(rg), 30000) === true) return rg;
  }
  return g;
}

// ---------- Rendering ----------
function computeCellSize() {
  const wrap = boardEl.parentElement;
  let avail;
  if (wrap && wrap.clientWidth > 0) {
    const cs = getComputedStyle(wrap);
    avail = wrap.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight);
  } else {
    avail = Math.min(460, window.innerWidth - 48);
  }
  cellSize = Math.max(12, Math.floor(avail / cols) - GAP_X);
}

function boardWidth() { return cols * cellSize + (cols - 1) * GAP_X + PADDING * 2; }
function boardHeight() { return rows * cellSize + (rows - 1) * GAP_Y + PADDING * 2 + SHADOW_DEPTH; }

function setBoardSize() {
  boardEl.style.width = boardWidth() + 'px';
  boardEl.style.height = boardHeight() + 'px';
}

function positionTile(el, r, c) {
  const x = PADDING + c * (cellSize + GAP_X);
  const y = PADDING + r * (cellSize + GAP_Y);
  el.style.setProperty('--x', x + 'px');
  el.style.setProperty('--y', y + 'px');
}

function positionCell(el, r, c) {
  const x = PADDING + c * (cellSize + GAP_X) - GAP_X / 2;
  const y = PADDING + r * (cellSize + GAP_Y) - GAP_Y / 2;
  el.style.setProperty('--x', x + 'px');
  el.style.setProperty('--y', y + 'px');
}

function setupBoard() {
  computeCellSize();
  setBoardSize();
  boardEl.innerHTML = '';
  tiles.clear();
  tileIds = Array.from({ length: rows }, () => new Array(cols).fill(-1));

  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const slot = document.createElement('div');
      slot.className = 'slot';
      slot.style.width = cellSize + 'px';
      slot.style.height = cellSize + 'px';
      positionTile(slot, r, c);
      boardEl.appendChild(slot);
    }
  }

  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const v = grid[r][c];
      if (v < 0) continue;
      const id = nextTileId++;
      tileIds[r][c] = id;
      const el = document.createElement('div');
      el.className = 'cell';
      el.style.width = (cellSize + GAP_X) + 'px';
      el.style.height = (cellSize + GAP_Y) + 'px';
      el.style.fontSize = Math.round(cellSize * 0.55) + 'px';
      el.style.setProperty('--face-x', (GAP_X / 2) + 'px');
      el.style.setProperty('--face-y', (GAP_Y / 2) + 'px');
      el.style.setProperty('--face-w', cellSize + 'px');
      el.style.setProperty('--face-h', cellSize + 'px');
      el.style.setProperty('--shadow', `0 ${SHADOW_DEPTH}px 0 ${SHADOW_PALETTE[v]}`);
      el.style.setProperty('--tile-color', `${PALETTE[v]}`);
      el.dataset.id = id;
      el.dataset.color = v;
      if (easterColor !== null && v === easterColor) el.dataset.andreaMatch = '';
      positionCell(el, r, c);
      boardEl.appendChild(el);
      tiles.set(id, { el, r, c });
    }
  }
}

function layoutTiles() {
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const id = tileIds[r][c];
      if (id < 0) continue;
      const t = tiles.get(id);
      t.r = r; t.c = c;
      positionCell(t.el, r, c);
    }
  }
}

function updateHoverClasses() {
  for (const { el } of tiles.values()) el.classList.remove('hover');
  for (const key of hoverGroup) {
    const r = Math.floor(key / cols), c = key % cols;
    const id = tileIds[r] && tileIds[r][c];
    if (id && id > 0) tiles.get(id).el.classList.add('hover');
  }
}

function updatePowerUpBadges() {
  const map = {
    rotateCW: document.getElementById('pu-rotate-cw'),
    rotateCCW: document.getElementById('pu-rotate-ccw'),
    clearRow: document.getElementById('pu-clear-row'),
    clearCol: document.getElementById('pu-clear-col'),
    bomb: document.getElementById('pu-bomb'),
    undo: document.getElementById('pu-undo'),
    hint: document.getElementById('hint'),
  };
  for (const key of Object.keys(map)) {
    const btn = map[key];
    if (!btn) continue;
    const amount = powerUps[key];
    const badge = btn.querySelector('.badge');
    if (badge) badge.textContent = amount;
    let disabled = amount <= 0 || busy;
    if (key === 'undo') {
      disabled = disabled || undoStack.length === 0;
    } else {
      disabled = disabled || gameOver;
    }
    btn.disabled = disabled;
    btn.classList.toggle('active', activePowerUp === key);
  }
  boardEl.classList.toggle('line-mode', activePowerUp === 'clearRow' || activePowerUp === 'clearCol');
}

function awardPowerUpFromTile(tileId) {
  const info = tilePowerUps.get(tileId);
  if (!info) return null;
  powerUps[info.key] += 1;
  tilePowerUps.delete(tileId);
  return info.key;
}

function renderTilePowerUp(tileEl, key, remaining) {
  const wrap = document.createElement('div');
  wrap.className = 'tile-powerup';
  const icon = document.createElement('i');
  icon.className = `hgi hgi-stroke hgi-rounded ${POWER_UP_ICONS[key]}`;
  const countEl = document.createElement('span');
  countEl.className = 'tile-powerup-count';
  countEl.textContent = remaining;
  wrap.appendChild(icon);
  wrap.appendChild(countEl);
  tileEl.appendChild(wrap);
}

function spawnLevelPowerUp() {
  const ids = Array.from(tiles.keys());
  if (!ids.length) return;
  const tileId = ids[Math.floor(Math.random() * ids.length)];
  const key = POWER_UP_KEYS[Math.floor(Math.random() * POWER_UP_KEYS.length)];
  tilePowerUps.set(tileId, { key, remaining: POWER_UP_TILE_TTL });
  const tile = tiles.get(tileId);
  if (!tile) return;
  renderTilePowerUp(tile.el, key, POWER_UP_TILE_TTL);
}

function decrementTilePowerUps() {
  for (const tid of Array.from(tilePowerUps.keys())) {
    const info = tilePowerUps.get(tid);
    info.remaining -= 1;
    const tile = tiles.get(tid);
    if (info.remaining <= 0) {
      tilePowerUps.delete(tid);
      if (tile) {
        const pu = tile.el.querySelector('.tile-powerup');
        if (pu) pu.remove();
      }
    } else if (tile) {
      const countEl = tile.el.querySelector('.tile-powerup-count');
      if (countEl) countEl.textContent = info.remaining;
    }
  }
}

function snapshotState() {
  const puByPos = new Map();
  for (const [tid, info] of tilePowerUps) {
    const t = tiles.get(tid);
    if (t) puByPos.set(`${t.r},${t.c}`, { key: info.key, remaining: info.remaining });
  }
  return {
    grid: cloneGrid(grid),
    rows, cols, numColors,
    score, moves, level,
    powerUps: { ...powerUps },
    puByPos,
  };
}

function pushSnapshot() {
  undoStack.push(snapshotState());
  if (undoStack.length > UNDO_STACK_MAX) undoStack.shift();
}

function clearUndoStack() {
  undoStack.length = 0;
}

function doUndo() {
  if (busy) return;
  if (powerUps.undo <= 0) return;
  if (undoStack.length === 0) return;
  haptic.confirm();

  if (pendingLevelTimeout !== null) {
    clearTimeout(pendingLevelTimeout);
    pendingLevelTimeout = null;
  }

  const snap = undoStack.pop();
  const newUndoCount = Math.max(0, powerUps.undo - 1);

  rows = snap.rows;
  cols = snap.cols;
  numColors = snap.numColors;
  grid = cloneGrid(snap.grid);
  score = snap.score;
  moves = snap.moves;
  level = snap.level;
  powerUps = { ...snap.powerUps, undo: newUndoCount };
  activePowerUp = null;
  tilePowerUps.clear();
  hoverGroup = new Set();
  gameOver = false;
  hideGameOver();

  setupBoard();

  for (const [posKey, info] of snap.puByPos) {
    const [r, c] = posKey.split(',').map(Number);
    const tid = tileIds[r] && tileIds[r][c];
    if (tid > 0) {
      tilePowerUps.set(tid, { key: info.key, remaining: info.remaining });
      const tile = tiles.get(tid);
      if (tile) renderTilePowerUp(tile.el, info.key, info.remaining);
    }
  }

  updateStatus();
  updatePowerUpBadges();
}

function rebuildSlots() {
  for (const s of boardEl.querySelectorAll('.slot')) s.remove();
  const frag = document.createDocumentFragment();
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const slot = document.createElement('div');
      slot.className = 'slot';
      slot.style.width = cellSize + 'px';
      slot.style.height = cellSize + 'px';
      positionTile(slot, r, c);
      frag.appendChild(slot);
    }
  }
  boardEl.prepend(frag);
}

function resizeTiles() {
  for (const { el } of tiles.values()) {
    el.style.width = (cellSize + GAP_X) + 'px';
    el.style.height = (cellSize + GAP_Y) + 'px';
    el.style.fontSize = Math.round(cellSize * 0.55) + 'px';
    el.style.setProperty('--face-w', cellSize + 'px');
    el.style.setProperty('--face-h', cellSize + 'px');
  }
}

async function doRotate(key) {
  if (busy || gameOver) return;
  if (powerUps[key] <= 0) return;
  haptic.confirm();
  pushSnapshot();
  busy = true;
  activePowerUp = null;
  hoverGroup = new Set();
  updateHoverClasses();

  // The CW button rotates CCW visually (per user preference), and vice versa.
  const cw = key === 'rotateCCW';
  const R = rows, C = cols;
  const nR = C, nC = R;
  const ng = Array.from({ length: nR }, () => new Array(nC).fill(-1));
  const nti = Array.from({ length: nR }, () => new Array(nC).fill(-1));
  for (let r = 0; r < R; r++) {
    for (let c = 0; c < C; c++) {
      const nr = cw ? c : (C - 1 - c);
      const nc = cw ? (R - 1 - r) : r;
      ng[nr][nc] = grid[r][c];
      nti[nr][nc] = tileIds[r][c];
    }
  }
  grid = ng;
  tileIds = nti;
  rows = nR;
  cols = nC;

  applyGravity(grid, tileIds);

  computeCellSize();
  setBoardSize();
  rebuildSlots();
  resizeTiles();
  layoutTiles();

  powerUps[key] -= 1;
  moves++;
  decrementTilePowerUps();
  updateStatus();
  updatePowerUpBadges();

  await wait(SLIDE_MS);
  busy = false;
  updatePowerUpBadges();
  checkEnd();
}

async function clearTargets(targets, powerUpKey) {
  if (!targets.length) return;
  haptic.confirm();
  pushSnapshot();
  busy = true;
  activePowerUp = null;
  hoverGroup = new Set();
  updateHoverClasses();

  const gained = targets.length * (targets.length - 1) * level;
  spawnScorePop(targets, gained);

  for (const [r, c] of targets) {
    const id = tileIds[r][c];
    if (id > 0) tiles.get(id).el.classList.add('clearing');
  }
  await wait(FADE_MS);

  for (const [r, c] of targets) {
    const id = tileIds[r][c];
    if (id > 0) {
      awardPowerUpFromTile(id);
      const tile = tiles.get(id);
      if (tile) tile.el.remove();
      tiles.delete(id);
    }
    grid[r][c] = -1;
    tileIds[r][c] = -1;
  }

  applyGravity(grid, tileIds);
  layoutTiles();
  score += gained;
  powerUps[powerUpKey] -= 1;
  moves++;
  decrementTilePowerUps();
  updateStatus();
  updatePowerUpBadges();
  maybeAnnounceRank();

  await wait(SLIDE_MS);
  busy = false;
  updatePowerUpBadges();
  checkEnd();
}

async function explodeBomb(r, c) {
  const color = grid[r][c];
  if (color < 0) return;
  const targets = [];
  for (let rr = 0; rr < rows; rr++)
    for (let cc = 0; cc < cols; cc++)
      if (grid[rr][cc] === color) targets.push([rr, cc]);
  await clearTargets(targets, 'bomb');
}

async function clearRow(r) {
  const targets = [];
  for (let cc = 0; cc < cols; cc++)
    if (grid[r][cc] >= 0) targets.push([r, cc]);
  await clearTargets(targets, 'clearRow');
}

async function clearCol(c) {
  const targets = [];
  for (let rr = 0; rr < rows; rr++)
    if (grid[rr][c] >= 0) targets.push([rr, c]);
  await clearTargets(targets, 'clearCol');
}

function updateStatus() {
  scoreEl.textContent = score;
  remainingEl.textContent = countRemaining(grid);
  movesEl.textContent = moves;
  if (levelEl) levelEl.textContent = level;
}

function wait(ms) { return new Promise((r) => setTimeout(r, ms)); }

function spawnScorePop(group, points) {
  const wrapRect = boardWrapEl.getBoundingClientRect();
  let sx = 0, sy = 0, count = 0;
  for (const [r, c] of group) {
    const id = tileIds[r] && tileIds[r][c];
    if (!id || id < 0) continue;
    const tile = tiles.get(id);
    if (!tile) continue;
    const rect = tile.el.getBoundingClientRect();
    sx += rect.left + rect.width / 2;
    sy += rect.top + rect.height / 2;
    count++;
  }
  if (!count) return;
  const x = sx / count - wrapRect.left;
  const y = sy / count - wrapRect.top;

  const pop = document.createElement('div');
  pop.className = 'score-pop';
  pop.textContent = '+' + points;
  pop.style.left = x + 'px';
  pop.style.top = y + 'px';
  const size = Math.min(56, 18 + Math.sqrt(points) * 4);
  pop.style.fontSize = size + 'px';
  boardWrapEl.appendChild(pop);
  pop.addEventListener('animationend', () => pop.remove());
}

// ---------- Interaction ----------
function tileFromEvent(e) {
  const target = e.target.closest('.cell');
  if (!target) return null;
  const id = +target.dataset.id;
  return tiles.get(id) || null;
}

boardEl.addEventListener('mousemove', (e) => {
  if (busy) return;
  const t = tileFromEvent(e);
  if (!t) return clearHover();
  if (grid[t.r][t.c] < 0) return clearHover();

  const next = new Set();
  if (activePowerUp === 'clearRow') {
    for (let cc = 0; cc < cols; cc++) {
      if (tileIds[t.r][cc] > 0) next.add(t.r * cols + cc);
    }
  } else if (activePowerUp === 'clearCol') {
    for (let rr = 0; rr < rows; rr++) {
      if (tileIds[rr][t.c] > 0) next.add(rr * cols + t.c);
    }
  } else {
    const group = findGroup(grid, t.r, t.c);
    if (group.length >= 2) group.forEach(([gr, gc]) => next.add(gr * cols + gc));
  }

  if (!sameSet(next, hoverGroup)) {
    hoverGroup = next;
    updateHoverClasses();
  }
});
boardEl.addEventListener('mouseleave', clearHover);

function clearHover() {
  if (hoverGroup.size === 0) return;
  hoverGroup = new Set();
  updateHoverClasses();
}

function sameSet(a, b) {
  if (a.size !== b.size) return false;
  for (const x of a) if (!b.has(x)) return false;
  return true;
}

boardEl.addEventListener('click', async (e) => {
  if (gameOver || busy) return;
  const t = tileFromEvent(e);
  if (!t) return;
  if (grid[t.r][t.c] < 0) return;
  if (activePowerUp === 'bomb') {
    await explodeBomb(t.r, t.c);
    return;
  }
  if (activePowerUp === 'clearRow') {
    await clearRow(t.r);
    return;
  }
  if (activePowerUp === 'clearCol') {
    await clearCol(t.c);
    return;
  }
  const group = findGroup(grid, t.r, t.c);
  if (group.length < 2) return;

  haptic();
  pushSnapshot();
  busy = true;
  hoverGroup = new Set();
  updateHoverClasses();

  const gained = group.length * (group.length - 1) * level;
  spawnScorePop(group, gained);

  // Fade out the cleared tiles.
  for (const [gr, gc] of group) {
    const id = tileIds[gr][gc];
    if (id > 0) tiles.get(id).el.classList.add('clearing');
  }
  await wait(FADE_MS);

  // Remove from data and DOM.
  let awarded = false;
  for (const [gr, gc] of group) {
    const id = tileIds[gr][gc];
    if (id > 0) {
      if (awardPowerUpFromTile(id)) { awarded = true; haptic.confirm(); }
      const tile = tiles.get(id);
      if (tile) tile.el.remove();
      tiles.delete(id);
    }
    grid[gr][gc] = -1;
    tileIds[gr][gc] = -1;
  }

  // Apply gravity + horizontal compaction to both grids, then slide.
  applyGravity(grid, tileIds);
  layoutTiles();
  score += gained;
  moves++;
  decrementTilePowerUps();
  updateStatus();
  if (awarded) updatePowerUpBadges();
  maybeAnnounceRank();

  await wait(SLIDE_MS);
  busy = false;
  updatePowerUpBadges();
  checkEnd();
});

function checkEnd() {
  if (isEmpty(grid)) {
    score += 100 * level;
    scoreEl.textContent = score;
    maybeAnnounceRank();
    gameOver = true;
    haptic.confirm();
    const nextLevel = level + 1;
    pendingLevelTimeout = setTimeout(() => {
      pendingLevelTimeout = null;
      startLevel(nextLevel, /*keepScore*/ true);
    }, 300);
    return;
  }
  const groups = findAllGroups(grid);
  if (groups.length === 0) {
    gameOver = true;
    haptic.error();
    showGameOver();
  }
}

function showGameOver() {
  const overlay = document.getElementById('game-over');
  const goLevel = document.getElementById('go-level');
  const goScore = document.getElementById('go-score');
  const continueBtn = document.getElementById('go-continue');
  const restartBtn = document.getElementById('go-restart');
  if (goLevel) goLevel.textContent = level;
  if (goScore) goScore.textContent = score;

  const usable =
    powerUps.rotateCW +
    powerUps.rotateCCW +
    powerUps.clearRow +
    powerUps.clearCol +
    powerUps.bomb +
    powerUps.undo;
  if (continueBtn) continueBtn.hidden = usable <= 0;
  if (restartBtn) restartBtn.classList.toggle('secondary', usable > 0);

  if (overlay) overlay.classList.add('show');
  openLeaderboard();
}

function doContinue() {
  gameOver = false;
  hideGameOver();
  haptic();
  updatePowerUpBadges();
}

function hideGameOver() {
  const overlay = document.getElementById('game-over');
  if (overlay) overlay.classList.remove('show');
}

// ---------- Leaderboard ----------
const LB_NAME_KEY = 'colorClearName';
const lbListEl = document.getElementById('lb-list');
const lbStatusEl = document.getElementById('lb-status');
const lbFormEl = document.getElementById('lb-submit');
const lbNameEl = document.getElementById('lb-name');
const lbSubmitBtn = lbFormEl ? lbFormEl.querySelector('button') : null;
let lastSubmittedRun = null;
let currentTop = [];
let boardLoaded = false;

function topScore() {
  let best = null;
  for (const e of currentTop) {
    if (best === null || e.score > best) best = e.score;
  }
  return best;
}

function evaluateCanSubmit() {
  if (!lbSubmitBtn || !lbNameEl) return;
  if (!boardLoaded) {
    lbSubmitBtn.disabled = true;
    return;
  }
  const name = (lbNameEl.value || '').trim();
  if (!name) {
    lbSubmitBtn.disabled = true;
    return;
  }
  const best = topScore();
  if (best !== null && score <= best) {
    lbSubmitBtn.disabled = true;
    if (lbStatusEl) {
      lbStatusEl.textContent = `High score is ${best} — beat it to submit.`;
      lbStatusEl.hidden = false;
    }
  } else {
    lbSubmitBtn.disabled = false;
    if (lbStatusEl && currentTop.length) lbStatusEl.hidden = true;
  }
}

function renderLeaderboard(entries) {
  if (!lbListEl) return;
  lbListEl.innerHTML = '';
  if (!entries.length) {
    lbListEl.hidden = true;
    if (lbStatusEl) {
      lbStatusEl.textContent = 'No scores yet — be the first.';
      lbStatusEl.hidden = false;
    }
    return;
  }
  for (let i = 0; i < entries.length; i++) {
    const e = entries[i];
    const li = document.createElement('li');
    if (
      lastSubmittedRun &&
      e.name === lastSubmittedRun.name &&
      e.score === lastSubmittedRun.score &&
      e.at === lastSubmittedRun.at
    ) {
      li.classList.add('you');
    }
    li.innerHTML = `<span class="rank">${i + 1}.</span><span class="name"></span><span class="level">Lvl ${e.level ?? 1}</span><span class="score">${e.score}</span>`;
    li.querySelector('.name').textContent = e.name;
    lbListEl.appendChild(li);
  }
  lbListEl.hidden = false;
  if (lbStatusEl) lbStatusEl.hidden = true;
}

async function fetchLeaderboard() {
  try {
    const res = await fetch('/api/leaderboard');
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    const entries = await res.json();
    currentTop = entries;
    boardLoaded = true;
    renderLeaderboard(entries);
    evaluateCanSubmit();
  } catch (err) {
    currentTop = [];
    boardLoaded = false;
    if (lbStatusEl) {
      lbStatusEl.textContent = 'Leaderboard unavailable.';
      lbStatusEl.hidden = false;
    }
    if (lbListEl) lbListEl.hidden = true;
    if (lbSubmitBtn) lbSubmitBtn.disabled = true;
  }
}

async function submitScore(name) {
  const payload = { name, score, level };
  if (lbStatusEl) {
    lbStatusEl.textContent = 'Submitting…';
    lbStatusEl.hidden = false;
  }
  try {
    const res = await fetch('/api/leaderboard', {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify(payload),
    });
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    const data = await res.json();
    const top = Array.isArray(data.top) ? data.top : [];
    currentTop = top;
    const mine = top.find((e) => e.name === name && e.score === score);
    if (mine) lastSubmittedRun = mine;
    renderLeaderboard(top);
  } catch (err) {
    if (lbStatusEl) {
      lbStatusEl.textContent = 'Submit failed — try again.';
      lbStatusEl.hidden = false;
    }
  }
}

function openLeaderboard() {
  lastSubmittedRun = null;
  currentTop = [];
  boardLoaded = false;
  if (lbNameEl) {
    lbNameEl.value = localStorage.getItem(LB_NAME_KEY) || '';
    lbNameEl.disabled = false;
  }
  if (lbSubmitBtn) lbSubmitBtn.disabled = true;
  if (lbStatusEl) {
    lbStatusEl.textContent = 'Loading…';
    lbStatusEl.hidden = false;
  }
  if (lbListEl) lbListEl.hidden = true;
  fetchLeaderboard();
}

if (lbFormEl) {
  lbFormEl.addEventListener('submit', async (e) => {
    e.preventDefault();
    const name = (lbNameEl.value || '').trim().slice(0, 20);
    if (!name) return;
    const best = topScore();
    if (best !== null && score <= best) return;
    localStorage.setItem(LB_NAME_KEY, name);
    lbNameEl.disabled = true;
    if (lbSubmitBtn) lbSubmitBtn.disabled = true;
    await submitScore(name);
  });
}

if (lbNameEl) {
  lbNameEl.addEventListener('input', evaluateCanSubmit);
}

// ---------- In-game rank toast ----------
const toastEl = document.getElementById('game-toast');
let toastTimer = null;
let toastHideTimer = null;
let topScoresCache = [];
let lastAnnouncedRank = Infinity;

function showToast(msg) {
  if (!toastEl) return;
  toastEl.textContent = msg;
  toastEl.hidden = false;
  void toastEl.offsetWidth;
  toastEl.classList.add('show');
  if (toastTimer) clearTimeout(toastTimer);
  if (toastHideTimer) clearTimeout(toastHideTimer);
  toastTimer = setTimeout(() => {
    toastEl.classList.remove('show');
    toastHideTimer = setTimeout(() => { toastEl.hidden = true; }, 260);
  }, 2800);
}

async function refreshTopScoresCache() {
  try {
    const res = await fetch('/api/leaderboard');
    if (!res.ok) return;
    const entries = await res.json();
    topScoresCache = entries
      .map((e) => Number(e.score) || 0)
      .sort((a, b) => b - a);
  } catch {}
}

function rankForScore(s) {
  if (s <= 0) return null;
  const list = topScoresCache.slice(0, 10);
  let rank = 1;
  for (const v of list) {
    if (s > v) return rank;
    rank++;
  }
  return rank <= 10 ? rank : null;
}

function ordinal(n) {
  const mod100 = n % 100;
  if (mod100 >= 11 && mod100 <= 13) return n + 'th';
  switch (n % 10) {
    case 1: return n + 'st';
    case 2: return n + 'nd';
    case 3: return n + 'rd';
    default: return n + 'th';
  }
}

function maybeAnnounceRank() {
  if (gameOver) return;
  const r = rankForScore(score);
  if (r === null) return;
  if (r >= lastAnnouncedRank) return;
  lastAnnouncedRank = r;
  showToast(`You reached ${ordinal(r)} on the leaderboard!`);
}

// ---------- Easter egg ----------
const EASTER_CODE = 'andrea';
let easterBuffer = '';
let easterColor = null;

function applyEasterMatches() {
  for (const { el } of tiles.values()) {
    const color = Number(el.dataset.color);
    if (easterColor !== null && color === easterColor) {
      el.dataset.andreaMatch = '';
    } else {
      delete el.dataset.andreaMatch;
    }
  }
}

window.addEventListener('keydown', (e) => {
  if (!/^[a-zA-Z]$/.test(e.key)) return;
  easterBuffer = (easterBuffer + e.key.toLowerCase()).slice(-EASTER_CODE.length);
  if (easterBuffer !== EASTER_CODE) return;
  if (easterColor === null) {
    const presentColors = new Set();
    for (let r = 0; r < rows; r++)
      for (let c = 0; c < cols; c++)
        if (grid[r][c] >= 0) presentColors.add(grid[r][c]);
    const pool = Array.from(presentColors);
    if (!pool.length) return;
    easterColor = pool[Math.floor(Math.random() * pool.length)];
    showToast('Hi Andrea');
  } else {
    easterColor = null;
    showToast('Bye Andrea');
  }
  applyEasterMatches();
});

// Console helpers for local testing.
window.debugToast = (msg = 'Test toast') => showToast(msg);
window.debugRank = (rank = 10) => showToast(`You reached ${ordinal(rank)} on the leaderboard!`);

// ---------- New game / levels ----------
function startLevel(lvl, keepScore = false) {
  level = Math.max(1, lvl);
  const cfg = levelConfig(level);
  rows = cfg.rows; cols = cfg.cols; numColors = cfg.colors;

  setTimeout(() => {
    // Bigger clusters on early levels, more fragmented later.
    const matchChance = Math.max(0.35, 0.7 - (level - 1) * 0.04);
    grid = generateSolvable(rows, cols, numColors, matchChance);
    if (!keepScore) score = 0;
    moves = 0;
    gameOver = false;
    busy = false;
    hoverGroup = new Set();
    tilePowerUps.clear();
    clearUndoStack();
    setupBoard();
    if (level % 2 === 1) spawnLevelPowerUp();
    updateStatus();
    updatePowerUpBadges();
  }, 20);
}

function newGame() {
  powerUps = { ...STARTING_POWER_UPS };
  activePowerUp = null;
  tilePowerUps.clear();
  lastAnnouncedRank = Infinity;
  refreshTopScoresCache();
  hideGameOver();
  startLevel(1, false);
}

document.getElementById('go-restart').addEventListener('click', newGame);
document.getElementById('go-continue').addEventListener('click', doContinue);
document.getElementById('pu-rotate-cw').addEventListener('click', () => doRotate('rotateCW'));
document.getElementById('pu-rotate-ccw').addEventListener('click', () => doRotate('rotateCCW'));
function togglePowerUp(key) {
  if (busy || gameOver) return;
  if (powerUps[key] <= 0) return;
  activePowerUp = (activePowerUp === key) ? null : key;
  haptic();
  updatePowerUpBadges();
}
document.getElementById('pu-bomb').addEventListener('click', () => togglePowerUp('bomb'));
document.getElementById('pu-clear-row').addEventListener('click', () => togglePowerUp('clearRow'));
document.getElementById('pu-clear-col').addEventListener('click', () => togglePowerUp('clearCol'));
document.getElementById('pu-undo').addEventListener('click', doUndo);
document.getElementById('hint').addEventListener('click', () => {
  if (busy || gameOver) return;
  if (powerUps.hint <= 0) return;
  const groups = findAllGroups(grid);
  if (groups.length === 0) return;
  powerUps.hint -= 1;
  updatePowerUpBadges();
  groups.sort((a, b) => b.length - a.length);
  const group = groups[0];

  const pulsed = [];
  for (const [r, c] of group) {
    const id = tileIds[r][c];
    if (id > 0) {
      const t = tiles.get(id);
      if (t) { t.el.classList.add('pulse'); pulsed.push(t.el); }
    }
  }
  setTimeout(() => {
    for (const el of pulsed) el.classList.remove('pulse');
  }, 1800);
});

window.addEventListener('resize', () => {
  if (!grid.length) return;
  computeCellSize();
  setBoardSize();
  const slots = boardEl.querySelectorAll('.slot');
  let i = 0;
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const slot = slots[i++];
      if (!slot) continue;
      slot.style.width = cellSize + 'px';
      slot.style.height = cellSize + 'px';
      positionTile(slot, r, c);
    }
  }
  resizeTiles();
  layoutTiles();
});

// Kick off
newGame();
