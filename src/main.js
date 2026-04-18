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
const toastEl = document.getElementById('toast');

// ---------- Level curve ----------
// Gentle ramp: small boards + few colors early, grow gradually.
function levelConfig(lvl) {
  const steps = [
    { rows: 4,  cols: 4,  colors: 2 }, // 1
    { rows: 5,  cols: 5,  colors: 2 }, // 2
    { rows: 5,  cols: 5,  colors: 3 }, // 3
    { rows: 6,  cols: 6,  colors: 3 }, // 4
    { rows: 7,  cols: 6,  colors: 3 }, // 5
    { rows: 7,  cols: 7,  colors: 3 }, // 6
    { rows: 7,  cols: 7,  colors: 4 }, // 7
    { rows: 8,  cols: 8,  colors: 4 }, // 8
    { rows: 9,  cols: 8,  colors: 4 }, // 9
    { rows: 9,  cols: 9,  colors: 4 }, // 10
    { rows: 10, cols: 9,  colors: 4 }, // 11
    { rows: 10, cols: 10, colors: 4 }, // 12
    { rows: 10, cols: 10, colors: 5 }, // 13
    { rows: 11, cols: 10, colors: 5 }, // 14
    { rows: 12, cols: 10, colors: 5 }, // 15
    { rows: 12, cols: 12, colors: 5 }, // 16
    { rows: 12, cols: 12, colors: 6 }, // 17
  ];
  if (lvl <= steps.length) return steps[lvl - 1];
  // Beyond the table, keep nudging upward.
  const extra = lvl - steps.length;
  return {
    rows: Math.min(16, 12 + Math.floor(extra / 2)),
    cols: Math.min(16, 12 + Math.floor((extra + 1) / 2)),
    colors: Math.min(PALETTE.length, 6 + Math.floor(extra / 3)),
  };
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

function fragmentedGrid(R, C, K) {
  const g = Array.from({ length: R }, () => new Array(C).fill(-1));
  const MATCH_CHANCE = 0.35;
  for (let r = 0; r < R; r++) {
    for (let c = 0; c < C; c++) {
      if (Math.random() < MATCH_CHANCE) {
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

function generateSolvable(R, C, K) {
  for (let attempt = 0; attempt < 12; attempt++) {
    const g = fragmentedGrid(R, C, K);
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

function setToast(msg, cls = '') {
  toastEl.className = 'toast ' + cls;
  toastEl.textContent = msg;
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
  const group = findGroup(grid, t.r, t.c);
  const next = new Set();
  if (group.length >= 2) group.forEach(([gr, gc]) => next.add(gr * cols + gc));
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
  const group = findGroup(grid, t.r, t.c);
  if (group.length < 2) return;

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
  for (const [gr, gc] of group) {
    const id = tileIds[gr][gc];
    if (id > 0) {
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

  await wait(SLIDE_MS);
  busy = false;
  checkEnd();
});

function checkEnd() {
  if (isEmpty(grid)) {
    gameOver = true;
    score += 100;
    scoreEl.textContent = score;
    setToast(`Cleared level ${level}! +100 bonus — next up…`, 'win');
    const nextLevel = level + 1;
    setTimeout(() => startLevel(nextLevel, /*keepScore*/ true), 1200);
    return;
  }
  const groups = findAllGroups(grid);
  if (groups.length === 0) {
    gameOver = true;
    setToast(`No more moves on level ${level}. Game over.`, 'lose');
  }
}

// ---------- New game / levels ----------
function startLevel(lvl, keepScore = false) {
  level = Math.max(1, lvl);
  const cfg = levelConfig(level);
  rows = cfg.rows; cols = cfg.cols; numColors = cfg.colors;

  setToast(`Level ${level} — generating board…`);
  setTimeout(() => {
    grid = generateSolvable(rows, cols, numColors);
    if (!keepScore) score = 0;
    moves = 0;
    gameOver = false;
    busy = false;
    hoverGroup = new Set();
    setupBoard();
    updateStatus();
    setToast(`Level ${level}: ${rows}×${cols}, ${numColors} colors`);
  }, 20);
}

function newGame() {
  startLevel(1, false);
}

document.getElementById('new-game').addEventListener('click', newGame);
document.getElementById('hint').addEventListener('click', () => {
  if (busy) return;
  const groups = findAllGroups(grid);
  if (groups.length === 0) { setToast('No groups available.'); return; }
  groups.sort((a, b) => b.length - a.length);
  hoverGroup = new Set(groups[0].map(([r, c]) => r * cols + c));
  updateHoverClasses();
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
  for (const { el } of tiles.values()) {
    el.style.width = (cellSize + GAP_X) + 'px';
    el.style.height = (cellSize + GAP_Y) + 'px';
    el.style.setProperty('--face-w', cellSize + 'px');
    el.style.setProperty('--face-h', cellSize + 'px');
  }
  layoutTiles();
});

// Kick off
newGame();
