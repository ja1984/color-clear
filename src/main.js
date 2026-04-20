import { haptic } from 'ios-haptics';

// ---------- Palette ----------
const PALETTE = [
  '#ff5b6e', // red
  '#5ec8ff', // blue
  '#5ee08c', // green
  '#ffd166', // yellow
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

const STARTING_POWER_UPS = { rotateCW: 0, rotateCCW: 0, clearRow: 0, clearCol: 0, bomb: 0, hint: 3 };
let powerUps = { ...STARTING_POWER_UPS };
let activePowerUp = null;

const POWER_UP_ICONS = {
  rotateCW: 'hgi-rotate-clockwise',
  rotateCCW: 'hgi-rotate-02',
  clearRow: 'hgi-arrow-horizontal',
  clearCol: 'hgi-arrow-vertical',
  bomb: 'hgi-bomb',
  hint: 'hgi-idea-01',
};
const POWER_UP_KEYS = Object.keys(POWER_UP_ICONS);
let tilePowerUps = new Map(); // tileId -> powerUpKey

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
    hint: document.getElementById('hint'),
  };
  for (const key of Object.keys(map)) {
    const btn = map[key];
    if (!btn) continue;
    const amount = powerUps[key];
    const badge = btn.querySelector('.badge');
    if (badge) badge.textContent = amount;
    btn.disabled = amount <= 0 || busy || gameOver;
    btn.classList.toggle('active', activePowerUp === key);
  }
  boardEl.classList.toggle('line-mode', activePowerUp === 'clearRow' || activePowerUp === 'clearCol');
}

function awardPowerUpFromTile(tileId) {
  const key = tilePowerUps.get(tileId);
  if (!key) return null;
  powerUps[key] += 1;
  tilePowerUps.delete(tileId);
  return key;
}

function spawnLevelPowerUp() {
  const ids = Array.from(tiles.keys());
  if (!ids.length) return;
  const tileId = ids[Math.floor(Math.random() * ids.length)];
  const key = POWER_UP_KEYS[Math.floor(Math.random() * POWER_UP_KEYS.length)];
  tilePowerUps.set(tileId, key);
  const tile = tiles.get(tileId);
  if (!tile) return;
  const icon = document.createElement('i');
  icon.className = `hgi hgi-stroke hgi-rounded ${POWER_UP_ICONS[key]} tile-powerup`;
  tile.el.appendChild(icon);
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
  busy = true;
  activePowerUp = null;
  hoverGroup = new Set();
  updateHoverClasses();

  const gained = targets.length * (targets.length - 1);
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
  updateStatus();
  updatePowerUpBadges();

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
  busy = true;
  hoverGroup = new Set();
  updateHoverClasses();

  const gained = group.length * (group.length - 1);
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
  updateStatus();
  if (awarded) updatePowerUpBadges();

  await wait(SLIDE_MS);
  busy = false;
  updatePowerUpBadges();
  checkEnd();
});

function checkEnd() {
  if (isEmpty(grid)) {
    gameOver = true;
    score += 100;
    scoreEl.textContent = score;
    haptic.confirm();
    const nextLevel = level + 1;
    setTimeout(() => startLevel(nextLevel, /*keepScore*/ true), 300);
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
  if (goLevel) goLevel.textContent = level;
  if (goScore) goScore.textContent = score;
  if (overlay) overlay.classList.add('show');
  openLeaderboard();
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
let lastSubmittedRun = null;

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
    li.innerHTML = `<span class="rank">${i + 1}.</span><span class="name"></span><span class="score">${e.score}</span>`;
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
    renderLeaderboard(entries);
  } catch (err) {
    if (lbStatusEl) {
      lbStatusEl.textContent = 'Leaderboard unavailable.';
      lbStatusEl.hidden = false;
    }
    if (lbListEl) lbListEl.hidden = true;
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
  if (lbNameEl) {
    lbNameEl.value = localStorage.getItem(LB_NAME_KEY) || '';
    lbNameEl.disabled = false;
  }
  if (lbFormEl) {
    const btn = lbFormEl.querySelector('button');
    if (btn) btn.disabled = false;
  }
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
    localStorage.setItem(LB_NAME_KEY, name);
    lbNameEl.disabled = true;
    const btn = lbFormEl.querySelector('button');
    if (btn) btn.disabled = true;
    await submitScore(name);
  });
}

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
  hideGameOver();
  startLevel(1, false);
}

document.getElementById('go-restart').addEventListener('click', newGame);
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
