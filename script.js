const SIZE = 9;
const DIGITS = [1, 2, 3, 4, 5, 6, 7, 8, 9];
const STORAGE_KEY = "killer_sudoku_progress_v3";
const DEFAULT_DIFFICULTY = "expert";

const DIFFICULTY_CONFIG = {
  beginner: { label: "入门", clueCount: 44 },
  normal: { label: "普通", clueCount: 32 },
  hard: { label: "困难", clueCount: 22 },
  expert: { label: "专家", clueCount: 0 },
};

const CAGE_SIZE_WEIGHTS = {
  beginner: [
    { size: 1, weight: 4 },
    { size: 2, weight: 6 },
    { size: 3, weight: 4 },
    { size: 4, weight: 2 },
  ],
  normal: [
    { size: 1, weight: 3 },
    { size: 2, weight: 5 },
    { size: 3, weight: 5 },
    { size: 4, weight: 3 },
    { size: 5, weight: 2 },
  ],
  hard: [
    { size: 1, weight: 2 },
    { size: 2, weight: 4 },
    { size: 3, weight: 5 },
    { size: 4, weight: 4 },
    { size: 5, weight: 3 },
    { size: 6, weight: 1 },
  ],
  expert: [
    { size: 1, weight: 1 },
    { size: 2, weight: 3 },
    { size: 3, weight: 5 },
    { size: 4, weight: 4 },
    { size: 5, weight: 3 },
    { size: 6, weight: 2 },
  ],
};

const boardEl = document.getElementById("board");
const boardWrapEl = document.getElementById("boardWrap");
const statusTextEl = document.getElementById("statusText");
const difficultySelectEl = document.getElementById("difficultySelect");
const newGameBtn = document.getElementById("newGameBtn");
const hintBtn = document.getElementById("hintBtn");
const solveBtn = document.getElementById("solveBtn");
const resetBtn = document.getElementById("resetBtn");
const noteModeBtn = document.getElementById("noteModeBtn");
const eraseBtn = document.getElementById("eraseBtn");
const numberPadEl = document.getElementById("numberPad");

let currentDifficulty = DEFAULT_DIFFICULTY;
let solution = [];
let board = [];
let notes = [];
let cages = [];
let cageMap = [];
let cellRefs = [];
let lockedCells = new Set();
let selectedCell = null;
let noteMode = false;
let boardResizeObserver = null;

function keyOf(r, c) {
  return `${r}-${c}`;
}

function parseKey(key) {
  const match = /^([0-8])-([0-8])$/.exec(key);
  if (!match) {
    return null;
  }
  return { r: Number(match[1]), c: Number(match[2]) };
}

function randInt(max) {
  return Math.floor(Math.random() * max);
}

function shuffle(list) {
  const arr = [...list];
  for (let i = arr.length - 1; i > 0; i -= 1) {
    const j = randInt(i + 1);
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function makeEmptyGrid(fill = 0) {
  return Array.from({ length: SIZE }, () => Array(SIZE).fill(fill));
}

function cloneGrid(grid) {
  return grid.map((row) => [...row]);
}

function listAllCells() {
  const cells = [];
  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      cells.push({ r, c });
    }
  }
  return cells;
}

function getDifficultyMeta(id) {
  return DIFFICULTY_CONFIG[id] || DIFFICULTY_CONFIG[DEFAULT_DIFFICULTY];
}

function noteBit(num) {
  return 1 << (num - 1);
}

function hasNote(mask, num) {
  return (mask & noteBit(num)) !== 0;
}

function toggleNote(r, c, num) {
  notes[r][c] ^= noteBit(num);
}

function clearNotes(r, c) {
  notes[r][c] = 0;
}

function pattern(r, c) {
  return (r * 3 + Math.floor(r / 3) + c) % SIZE;
}

function generateSolvedBoard() {
  const numbers = shuffle(DIGITS);
  const rowBands = shuffle([0, 1, 2]);
  const colBands = shuffle([0, 1, 2]);

  const rows = rowBands.flatMap((band) => shuffle([0, 1, 2]).map((r) => band * 3 + r));
  const cols = colBands.flatMap((band) => shuffle([0, 1, 2]).map((c) => band * 3 + c));

  return rows.map((r) => cols.map((c) => numbers[pattern(r, c)]));
}

function pickWeighted(candidates) {
  const total = candidates.reduce((sum, item) => sum + item.weight, 0);
  let roll = Math.random() * total;
  for (const item of candidates) {
    roll -= item.weight;
    if (roll <= 0) {
      return item;
    }
  }
  return candidates[candidates.length - 1];
}

function neighborsOf(r, c) {
  const list = [];
  if (r > 0) {
    list.push({ r: r - 1, c });
  }
  if (r < SIZE - 1) {
    list.push({ r: r + 1, c });
  }
  if (c > 0) {
    list.push({ r, c: c - 1 });
  }
  if (c < SIZE - 1) {
    list.push({ r, c: c + 1 });
  }
  return list;
}

function pickCageTargetSize() {
  const pool = CAGE_SIZE_WEIGHTS[currentDifficulty] || CAGE_SIZE_WEIGHTS[DEFAULT_DIFFICULTY];
  return pickWeighted(pool).size;
}

function partitionIrregularCages() {
  const assigned = makeEmptyGrid(false);
  const shuffledStarts = shuffle(listAllCells());
  let cursor = 0;
  const built = [];

  function nextStart() {
    while (cursor < shuffledStarts.length) {
      const candidate = shuffledStarts[cursor];
      cursor += 1;
      if (!assigned[candidate.r][candidate.c]) {
        return candidate;
      }
    }
    for (let r = 0; r < SIZE; r += 1) {
      for (let c = 0; c < SIZE; c += 1) {
        if (!assigned[r][c]) {
          return { r, c };
        }
      }
    }
    return null;
  }

  let start = nextStart();
  while (start) {
    const targetSize = pickCageTargetSize();
    const cells = [start];
    assigned[start.r][start.c] = true;

    const frontier = [];
    const frontierSet = new Set();
    const pushFrontier = (pos) => {
      neighborsOf(pos.r, pos.c).forEach((n) => {
        if (assigned[n.r][n.c]) {
          return;
        }
        const k = keyOf(n.r, n.c);
        if (frontierSet.has(k)) {
          return;
        }
        frontierSet.add(k);
        frontier.push(n);
      });
    };
    pushFrontier(start);

    while (cells.length < targetSize && frontier.length > 0) {
      const idx = randInt(frontier.length);
      const next = frontier.splice(idx, 1)[0];
      frontierSet.delete(keyOf(next.r, next.c));
      if (assigned[next.r][next.c]) {
        continue;
      }
      assigned[next.r][next.c] = true;
      cells.push(next);
      pushFrontier(next);
    }

    built.push({ sum: 0, cells });
    start = nextStart();
  }

  return built;
}

function cageBounds(cage) {
  return cage.cells.reduce(
    (acc, cell) => ({
      minR: Math.min(acc.minR, cell.r),
      maxR: Math.max(acc.maxR, cell.r),
      minC: Math.min(acc.minC, cell.c),
      maxC: Math.max(acc.maxC, cell.c),
    }),
    { minR: SIZE, maxR: -1, minC: SIZE, maxC: -1 },
  );
}

function isRectangularCage(cage) {
  const b = cageBounds(cage);
  return (b.maxR - b.minR + 1) * (b.maxC - b.minC + 1) === cage.cells.length;
}

function cageLayoutLooksGood(layout) {
  const singles = layout.filter((cage) => cage.cells.length === 1).length;
  const irregular = layout.filter((cage) => cage.cells.length >= 3 && !isRectangularCage(cage)).length;
  const maxSinglesByDifficulty = {
    beginner: 18,
    normal: 14,
    hard: 11,
    expert: 9,
  };
  const maxSingles = maxSinglesByDifficulty[currentDifficulty] ?? 11;
  if (layout.length < 18 || layout.length > 58) {
    return false;
  }
  if (singles > maxSingles) {
    return false;
  }
  return irregular >= Math.max(5, Math.floor(layout.length * 0.2));
}

function generateCages(currentSolution) {
  for (let attempt = 0; attempt < 120; attempt += 1) {
    const built = partitionIrregularCages();
    if (!cageLayoutLooksGood(built)) {
      continue;
    }
    for (const cage of built) {
      cage.sum = cage.cells.reduce((sum, cell) => sum + currentSolution[cell.r][cell.c], 0);
    }
    return built;
  }

  const fallback = partitionIrregularCages();
  for (const cage of fallback) {
    cage.sum = cage.cells.reduce((sum, cell) => sum + currentSolution[cell.r][cell.c], 0);
  }
  return fallback;
}

function buildCageMap(currentCages) {
  const map = makeEmptyGrid(-1);
  currentCages.forEach((cage, index) => {
    cage.cells.forEach((cell) => {
      map[cell.r][cell.c] = index;
    });
  });
  return map;
}

function getTopLeftCell(cage) {
  return cage.cells.reduce((best, cell) => {
    if (!best) {
      return cell;
    }
    if (cell.r < best.r || (cell.r === best.r && cell.c < best.c)) {
      return cell;
    }
    return best;
  }, null);
}

function getBorderValue(r, c, edge) {
  if (edge === "top") {
    return r === 0 || r % 3 === 0 ? "2px solid var(--line-strong)" : "1px solid var(--line-soft)";
  }
  if (edge === "left") {
    return c === 0 || c % 3 === 0 ? "2px solid var(--line-strong)" : "1px solid var(--line-soft)";
  }
  if (edge === "right") {
    return c === SIZE - 1 ? "2px solid var(--line-strong)" : "";
  }
  return r === SIZE - 1 ? "2px solid var(--line-strong)" : "";
}

function createCageEdge(direction, r, c, unit, insetPx) {
  const edge = document.createElement("span");
  edge.className = `cage-edge ${direction}`;

  const leftPct = (c * unit).toFixed(6);
  const topPct = (r * unit).toFixed(6);
  const nextLeftPct = ((c + 1) * unit).toFixed(6);
  const nextTopPct = ((r + 1) * unit).toFixed(6);

  if (direction === "top") {
    edge.style.left = `calc(${leftPct}% + ${insetPx}px)`;
    edge.style.top = `calc(${topPct}% + ${insetPx}px)`;
    edge.style.width = `calc(${unit.toFixed(6)}% - ${insetPx * 2}px)`;
  } else if (direction === "left") {
    edge.style.left = `calc(${leftPct}% + ${insetPx}px)`;
    edge.style.top = `calc(${topPct}% + ${insetPx}px)`;
    edge.style.height = `calc(${unit.toFixed(6)}% - ${insetPx * 2}px)`;
  } else if (direction === "bottom") {
    edge.style.left = `calc(${leftPct}% + ${insetPx}px)`;
    edge.style.top = `calc(${nextTopPct}% - ${insetPx}px)`;
    edge.style.width = `calc(${unit.toFixed(6)}% - ${insetPx * 2}px)`;
  } else if (direction === "right") {
    edge.style.left = `calc(${nextLeftPct}% - ${insetPx}px)`;
    edge.style.top = `calc(${topPct}% + ${insetPx}px)`;
    edge.style.height = `calc(${unit.toFixed(6)}% - ${insetPx * 2}px)`;
  }

  return edge;
}

function renderCageLayer() {
  const unit = 100 / SIZE;
  const insetPx = 3;
  const layer = document.createElement("div");
  layer.className = "cage-layer";

  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      const id = cageMap[r][c];
      if (r === 0 || cageMap[r - 1][c] !== id) {
        layer.appendChild(createCageEdge("top", r, c, unit, insetPx));
      }
      if (c === 0 || cageMap[r][c - 1] !== id) {
        layer.appendChild(createCageEdge("left", r, c, unit, insetPx));
      }
      if (r === SIZE - 1 || cageMap[r + 1][c] !== id) {
        layer.appendChild(createCageEdge("bottom", r, c, unit, insetPx));
      }
      if (c === SIZE - 1 || cageMap[r][c + 1] !== id) {
        layer.appendChild(createCageEdge("right", r, c, unit, insetPx));
      }
    }
  }

  boardEl.appendChild(layer);
}

function setStatus(text, tone = "") {
  statusTextEl.textContent = text;
  statusTextEl.className = `status ${tone}`.trim();
}

function fitBoardSquare() {
  if (!boardWrapEl || !boardEl) {
    return;
  }
  const width = boardWrapEl.clientWidth;
  const height = boardWrapEl.clientHeight;
  const size = Math.floor(Math.min(width, height) - 4);
  if (size > 0) {
    boardEl.style.width = `${size}px`;
    boardEl.style.height = `${size}px`;
  }
}

function setNoteMode(enabled) {
  noteMode = enabled;
  noteModeBtn.classList.toggle("active", enabled);
  noteModeBtn.setAttribute("aria-pressed", enabled ? "true" : "false");
  noteModeBtn.textContent = enabled ? "备注 ON" : "备注 OFF";
}

function updateSelectedCellVisual() {
  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      cellRefs[r][c].cell.classList.remove("selected");
    }
  }

  if (selectedCell) {
    cellRefs[selectedCell.r][selectedCell.c].cell.classList.add("selected");
  }
}

function selectCell(r, c) {
  selectedCell = { r, c };
  updateSelectedCellVisual();
}

function moveSelection(dr, dc) {
  if (!selectedCell) {
    selectCell(0, 0);
    return;
  }
  const nr = Math.min(SIZE - 1, Math.max(0, selectedCell.r + dr));
  const nc = Math.min(SIZE - 1, Math.max(0, selectedCell.c + dc));
  selectCell(nr, nc);
}

function getSelectedPosition() {
  if (!selectedCell) {
    return null;
  }
  return selectedCell;
}

function updateCellDisplay(r, c) {
  const ref = cellRefs[r][c];
  const value = board[r][c];
  const mask = notes[r][c];

  ref.valueEl.textContent = value > 0 ? String(value) : "";
  ref.cell.classList.toggle("has-value", value > 0);

  for (let n = 1; n <= 9; n += 1) {
    ref.noteEls[n - 1].classList.toggle("visible", value === 0 && hasNote(mask, n));
  }
}

function renderBoard() {
  boardEl.innerHTML = "";
  cellRefs = makeEmptyGrid(null);
  const clueAt = new Map();

  cages.forEach((cage) => {
    const topLeft = getTopLeftCell(cage);
    clueAt.set(keyOf(topLeft.r, topLeft.c), cage.sum);
  });

  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      const cell = document.createElement("div");
      cell.className = "cell";
      cell.style.borderTop = getBorderValue(r, c, "top");
      cell.style.borderLeft = getBorderValue(r, c, "left");
      cell.style.borderRight = getBorderValue(r, c, "right");
      cell.style.borderBottom = getBorderValue(r, c, "bottom");

      if (lockedCells.has(keyOf(r, c))) {
        cell.classList.add("given");
      }

      const clue = clueAt.get(keyOf(r, c));
      if (clue !== undefined) {
        const clueEl = document.createElement("span");
        clueEl.className = "clue";
        clueEl.textContent = String(clue);
        cell.appendChild(clueEl);
      }

      const notesEl = document.createElement("div");
      notesEl.className = "notes-grid";
      const noteEls = [];
      for (let n = 1; n <= 9; n += 1) {
        const note = document.createElement("span");
        note.className = "note";
        note.textContent = String(n);
        noteEls.push(note);
        notesEl.appendChild(note);
      }
      cell.appendChild(notesEl);

      const valueEl = document.createElement("div");
      valueEl.className = "cell-value";
      cell.appendChild(valueEl);

      cell.addEventListener("click", () => selectCell(r, c));

      boardEl.appendChild(cell);
      cellRefs[r][c] = { cell, valueEl, noteEls };
      updateCellDisplay(r, c);
    }
  }

  renderCageLayer();
  updateSelectedCellVisual();
  fitBoardSquare();
}

function clearCellMarks() {
  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      const cls = cellRefs[r][c].cell.classList;
      cls.remove("value-error", "hint");
      if (lockedCells.has(keyOf(r, c))) {
        cls.add("given");
      } else {
        cls.remove("given");
      }
    }
  }
}

function markValueErrors(cells) {
  cells.forEach(({ r, c }) => {
    if (board[r][c] > 0) {
      cellRefs[r][c].cell.classList.add("value-error");
    }
  });
}

function collectDuplicateCells(getValueByIndex) {
  const duplicates = [];
  for (let i = 0; i < SIZE; i += 1) {
    const positionsByNumber = new Map();
    for (let j = 0; j < SIZE; j += 1) {
      const pos = getValueByIndex(i, j);
      if (pos.value === 0) {
        continue;
      }
      if (!positionsByNumber.has(pos.value)) {
        positionsByNumber.set(pos.value, []);
      }
      positionsByNumber.get(pos.value).push({ r: pos.r, c: pos.c });
    }
    for (const list of positionsByNumber.values()) {
      if (list.length > 1) {
        duplicates.push(...list);
      }
    }
  }
  return duplicates;
}

function validateBoard({ silentStatus = false } = {}) {
  clearCellMarks();
  const invalidKeySet = new Set();

  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      if (board[r][c] > 0 && board[r][c] !== solution[r][c]) {
        invalidKeySet.add(keyOf(r, c));
      }
    }
  }

  const rowDupes = collectDuplicateCells((r, c) => ({ r, c, value: board[r][c] }));
  const colDupes = collectDuplicateCells((c, r) => ({ r, c, value: board[r][c] }));
  const boxDupes = collectDuplicateCells((box, offset) => {
    const br = Math.floor(box / 3) * 3;
    const bc = (box % 3) * 3;
    const r = br + Math.floor(offset / 3);
    const c = bc + (offset % 3);
    return { r, c, value: board[r][c] };
  });
  [...rowDupes, ...colDupes, ...boxDupes].forEach(({ r, c }) => invalidKeySet.add(keyOf(r, c)));

  cages.forEach((cage) => {
    let sum = 0;
    let filled = 0;
    cage.cells.forEach(({ r, c }) => {
      if (board[r][c] > 0) {
        sum += board[r][c];
        filled += 1;
      }
    });
    if (sum > cage.sum || (filled === cage.cells.length && sum !== cage.sum)) {
      cage.cells.forEach(({ r, c }) => {
        if (board[r][c] > 0) {
          invalidKeySet.add(keyOf(r, c));
        }
      });
    }
  });

  const invalidCells = [...invalidKeySet].map((k) => parseKey(k)).filter(Boolean);
  markValueErrors(invalidCells);
  const hasError = invalidCells.length > 0;
  const complete = board.every((row) => row.every((value) => value > 0));

  if (!silentStatus) {
    if (complete && !hasError) {
      setStatus("完成！你同时满足了数独规则和虚线求和规则。", "ok");
    } else if (hasError) {
      setStatus("存在错误：红色数字需要修正。", "warn");
    } else {
      setStatus("进行中。");
    }
  }
  return !hasError;
}

function clearPeerNotes(r, c, num) {
  const bit = noteBit(num);
  const affected = new Set();

  for (let i = 0; i < SIZE; i += 1) {
    if (i !== c && (notes[r][i] & bit) !== 0) {
      notes[r][i] &= ~bit;
      affected.add(keyOf(r, i));
    }
    if (i !== r && (notes[i][c] & bit) !== 0) {
      notes[i][c] &= ~bit;
      affected.add(keyOf(i, c));
    }
  }

  const br = Math.floor(r / 3) * 3;
  const bc = Math.floor(c / 3) * 3;
  for (let rr = br; rr < br + 3; rr += 1) {
    for (let cc = bc; cc < bc + 3; cc += 1) {
      if (rr === r && cc === c) {
        continue;
      }
      if ((notes[rr][cc] & bit) !== 0) {
        notes[rr][cc] &= ~bit;
        affected.add(keyOf(rr, cc));
      }
    }
  }

  affected.forEach((k) => {
    const pos = parseKey(k);
    if (pos) {
      updateCellDisplay(pos.r, pos.c);
    }
  });
}

function applyDifficultyClues() {
  board = makeEmptyGrid(0);
  notes = makeEmptyGrid(0);
  lockedCells = new Set();
  const clueCount = Math.min(getDifficultyMeta(currentDifficulty).clueCount, SIZE * SIZE);
  const picks = shuffle(listAllCells());

  for (let i = 0; i < clueCount; i += 1) {
    const pos = picks[i];
    board[pos.r][pos.c] = solution[pos.r][pos.c];
    lockedCells.add(keyOf(pos.r, pos.c));
  }
}

function normalizeLockedKeys(rawKeys) {
  const normalized = new Set();
  rawKeys.forEach((key) => {
    const pos = parseKey(String(key));
    if (!pos) {
      return;
    }
    if (board[pos.r][pos.c] > 0) {
      normalized.add(keyOf(pos.r, pos.c));
    }
  });
  return normalized;
}

function saveGameState() {
  const payload = {
    version: 3,
    difficulty: currentDifficulty,
    solution,
    board,
    notes,
    cages,
    lockedCells: [...lockedCells],
    noteMode,
    selectedCell,
    savedAt: Date.now(),
  };

  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(payload));
  } catch (_error) {
    // Ignore storage failures.
  }
}

function isGridValid(grid, minValue, maxValue) {
  if (!Array.isArray(grid) || grid.length !== SIZE) {
    return false;
  }
  return grid.every(
    (row) =>
      Array.isArray(row) &&
      row.length === SIZE &&
      row.every((value) => Number.isInteger(value) && value >= minValue && value <= maxValue),
  );
}

function isCageListValid(cageList) {
  if (!Array.isArray(cageList) || cageList.length === 0) {
    return false;
  }

  const counter = makeEmptyGrid(0);
  for (const cage of cageList) {
    if (!cage || !Number.isInteger(cage.sum) || cage.sum <= 0 || !Array.isArray(cage.cells) || cage.cells.length < 1) {
      return false;
    }
    for (const cell of cage.cells) {
      if (!cell || !Number.isInteger(cell.r) || !Number.isInteger(cell.c)) {
        return false;
      }
      if (cell.r < 0 || cell.r >= SIZE || cell.c < 0 || cell.c >= SIZE) {
        return false;
      }
      counter[cell.r][cell.c] += 1;
    }
  }

  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      if (counter[r][c] !== 1) {
        return false;
      }
    }
  }
  return true;
}

function sanitizeCages(cageList) {
  return cageList.map((cage) => ({
    sum: cage.sum,
    cells: cage.cells.map((cell) => ({ r: cell.r, c: cell.c })),
  }));
}

function sanitizeSelectedCell(raw) {
  if (!raw || !Number.isInteger(raw.r) || !Number.isInteger(raw.c)) {
    return null;
  }
  if (raw.r < 0 || raw.r >= SIZE || raw.c < 0 || raw.c >= SIZE) {
    return null;
  }
  return { r: raw.r, c: raw.c };
}

function applyLoadedState(parsed) {
  currentDifficulty = DIFFICULTY_CONFIG[parsed.difficulty] ? parsed.difficulty : DEFAULT_DIFFICULTY;
  difficultySelectEl.value = currentDifficulty;
  solution = cloneGrid(parsed.solution);
  board = cloneGrid(parsed.board);
  notes = isGridValid(parsed.notes, 0, 511) ? cloneGrid(parsed.notes) : makeEmptyGrid(0);
  cages = sanitizeCages(parsed.cages);
  cageMap = buildCageMap(cages);
  lockedCells = normalizeLockedKeys(parsed.lockedCells);
  selectedCell = sanitizeSelectedCell(parsed.selectedCell);
  setNoteMode(Boolean(parsed.noteMode));
  renderBoard();
  validateBoard({ silentStatus: true });
  if (!selectedCell) {
    selectedCell = { r: 0, c: 0 };
    updateSelectedCellVisual();
  }
}

function loadSavedState() {
  let raw = null;
  try {
    raw = localStorage.getItem(STORAGE_KEY);
  } catch (_error) {
    return false;
  }
  if (!raw) {
    return false;
  }

  let parsed = null;
  try {
    parsed = JSON.parse(raw);
  } catch (_error) {
    return false;
  }

  if (!parsed || parsed.version !== 3) {
    return false;
  }
  if (!isGridValid(parsed.solution, 1, 9) || !isGridValid(parsed.board, 0, 9)) {
    return false;
  }
  if (!isCageListValid(parsed.cages) || !Array.isArray(parsed.lockedCells)) {
    return false;
  }

  applyLoadedState(parsed);
  setStatus(`已恢复上次进度（${getDifficultyMeta(currentDifficulty).label}）。`);
  return true;
}

function startNewGame(difficulty = currentDifficulty) {
  currentDifficulty = DIFFICULTY_CONFIG[difficulty] ? difficulty : DEFAULT_DIFFICULTY;
  difficultySelectEl.value = currentDifficulty;
  solution = generateSolvedBoard();
  cages = generateCages(solution);
  cageMap = buildCageMap(cages);
  applyDifficultyClues();
  selectedCell = { r: 0, c: 0 };
  setNoteMode(false);
  renderBoard();
  validateBoard({ silentStatus: true });
  setStatus(`新题已生成（${getDifficultyMeta(currentDifficulty).label}）。`);
  saveGameState();
}

function fillHint() {
  const options = [];
  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      if (board[r][c] === 0) {
        options.push({ r, c });
      }
    }
  }

  if (!options.length) {
    setStatus("没有可提示的空格。");
    return;
  }

  const pick = options[randInt(options.length)];
  const value = solution[pick.r][pick.c];
  board[pick.r][pick.c] = value;
  clearNotes(pick.r, pick.c);
  clearPeerNotes(pick.r, pick.c, value);
  lockedCells.add(keyOf(pick.r, pick.c));
  updateCellDisplay(pick.r, pick.c);
  validateBoard({ silentStatus: true });
  cellRefs[pick.r][pick.c].cell.classList.add("hint", "given");
  setStatus(`已提示：第 ${pick.r + 1} 行第 ${pick.c + 1} 列。`);
  saveGameState();
}

function revealAnswer() {
  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      board[r][c] = solution[r][c];
      clearNotes(r, c);
      lockedCells.add(keyOf(r, c));
      updateCellDisplay(r, c);
      cellRefs[r][c].cell.classList.add("given");
    }
  }
  validateBoard({ silentStatus: true });
  setStatus("答案已揭晓。");
  saveGameState();
}

function resetInputs() {
  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      if (lockedCells.has(keyOf(r, c))) {
        continue;
      }
      board[r][c] = 0;
      clearNotes(r, c);
      updateCellDisplay(r, c);
    }
  }
  validateBoard({ silentStatus: true });
  setStatus("已清空可编辑输入。");
  saveGameState();
}

function clearSelectedCell() {
  const pos = getSelectedPosition();
  if (!pos) {
    setStatus("请先选择一个格子。");
    return;
  }
  if (lockedCells.has(keyOf(pos.r, pos.c))) {
    setStatus("该格是题目给定数字，不能修改。", "warn");
    return;
  }

  board[pos.r][pos.c] = 0;
  clearNotes(pos.r, pos.c);
  updateCellDisplay(pos.r, pos.c);
  validateBoard();
  saveGameState();
}

function applyDigitToSelected(num) {
  const pos = getSelectedPosition();
  if (!pos) {
    setStatus("请先选择一个格子。");
    return;
  }
  if (lockedCells.has(keyOf(pos.r, pos.c))) {
    setStatus("该格是题目给定数字，不能修改。", "warn");
    return;
  }

  if (noteMode) {
    if (board[pos.r][pos.c] !== 0) {
      setStatus("备注模式下，请先清除该格中的正式数字。", "warn");
      return;
    }
    toggleNote(pos.r, pos.c, num);
    updateCellDisplay(pos.r, pos.c);
    validateBoard({ silentStatus: true });
    saveGameState();
    return;
  }

  board[pos.r][pos.c] = num;
  clearNotes(pos.r, pos.c);
  clearPeerNotes(pos.r, pos.c, num);
  updateCellDisplay(pos.r, pos.c);
  validateBoard();
  saveGameState();
}

function handleBoardKeydown(event) {
  const tag = document.activeElement ? document.activeElement.tagName : "";
  if (tag === "SELECT" || tag === "INPUT" || tag === "TEXTAREA") {
    return;
  }

  if (event.key === "ArrowUp") {
    event.preventDefault();
    moveSelection(-1, 0);
    return;
  }
  if (event.key === "ArrowDown") {
    event.preventDefault();
    moveSelection(1, 0);
    return;
  }
  if (event.key === "ArrowLeft") {
    event.preventDefault();
    moveSelection(0, -1);
    return;
  }
  if (event.key === "ArrowRight") {
    event.preventDefault();
    moveSelection(0, 1);
    return;
  }
  if (event.key >= "1" && event.key <= "9") {
    event.preventDefault();
    applyDigitToSelected(Number(event.key));
    return;
  }
  if (event.key === "Delete" || event.key === "Backspace" || event.key === "0") {
    event.preventDefault();
    clearSelectedCell();
  }
}

newGameBtn.addEventListener("click", () => startNewGame(difficultySelectEl.value));
hintBtn.addEventListener("click", fillHint);
solveBtn.addEventListener("click", revealAnswer);
resetBtn.addEventListener("click", resetInputs);
difficultySelectEl.addEventListener("change", () => startNewGame(difficultySelectEl.value));
noteModeBtn.addEventListener("click", () => {
  setNoteMode(!noteMode);
  saveGameState();
});
eraseBtn.addEventListener("click", clearSelectedCell);
numberPadEl.addEventListener("click", (event) => {
  const target = event.target;
  if (!(target instanceof HTMLElement)) {
    return;
  }
  const raw = target.getAttribute("data-num");
  if (!raw) {
    return;
  }
  applyDigitToSelected(Number(raw));
});
document.addEventListener("keydown", handleBoardKeydown);
window.addEventListener("resize", fitBoardSquare);
if (typeof ResizeObserver !== "undefined" && boardWrapEl) {
  boardResizeObserver = new ResizeObserver(() => fitBoardSquare());
  boardResizeObserver.observe(boardWrapEl);
}

if (!loadSavedState()) {
  startNewGame(DEFAULT_DIFFICULTY);
}
