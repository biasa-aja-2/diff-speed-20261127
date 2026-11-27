// Fast line diff — a make.fun bounty entry.
//
// An independent implementation of makefun-diff 1.0.0's rule (RULES.txt):
// a text is cut after every '\n' (a '\r' is part of its line) and a last line
// with no '\n' is a line too; two lines are equal only when identical code
// units, newline presence included. The edit script keeps the common prefix,
// then the common suffix of what is left; between them Myers's greedy search
// keeps, on each diagonal, the path reaching furthest into the old text,
// prefers a deletion over an insertion when both reach the same point, never
// moves past either text's end, prunes no edge diagonal, and follows every
// run of equal lines as far as it goes; the first path to reach both ends
// wins. The patch is makefun-diff/1's own format (see below).
//
// Speed: lines are reduced to a cheap 31-bit hash sampled from a few code
// units (length, first, last and middle units), so the search's comparisons
// are single integer compares; a hash match is always confirmed with a real
// string compare, so equality is exact and no interning table is needed.
// The search runs on typed arrays, keeping only the live diagonals of each
// depth (so the work and the memory scale with the diagonals actually used),
// with the per-depth frontier kept for backtracking, and the middle slices
// carry a distinct sentinel each (values no line hash can take) so the snake
// loop needs no bounds checks. Two searches run: a banded one first, whose
// diagonals stay near the straight line from the first lines to the last,
// which finds an upper bound on the edit distance, and then the full search
// pruned to the diagonals that can still reach the end within that bound —
// the pruning is exact, since a diagonal that cannot reach the end within
// the bound cannot hold the winning path, and the banded search only ever
// supplies a valid bound (the length of a real edit script) or none at all.

/** The patch's first word. */
const FORMAT = 'makefun-diff/1';

/** The kept lines a hunk shows before and after each change run. */
const CONTEXT = 3;

const KEEP = 0;
const DELETE = 1;
const INSERT = 2;

/** How far the banded search lets a diagonal stray from the straight line. */
const BAND = 150;

/** The banded search gives up after this many edits and falls back. */
const BAND_CAP = 6000;

/** A text's lines, each with its '\n' (the last one without, when the text does not end in one). */
function splitLines(text) {
  const lines = [];
  let start = 0;
  for (;;) {
    const nl = text.indexOf('\n', start);
    if (nl === -1) {
      if (start < text.length) lines.push(text.slice(start));
      return lines;
    }
    lines.push(text.slice(start, nl + 1));
    start = nl + 1;
  }
}

/** A line's 31-bit hash, from its length and a few sampled code units. */
function hashLine(s) {
  const len = s.length;
  if (len === 0) return 0;
  let h = len * 2654435761;
  h ^= s.charCodeAt(0) * 40503;
  h ^= s.charCodeAt(len - 1) * 1031;
  h ^= s.charCodeAt(len >> 1) * 131;
  h ^= s.charCodeAt((len >> 2) | 0) * 17;
  return h & 0x7fffffff;
}

/**
 * Myers's greedy search over the middle slices a[0..n) and b[0..m).
 * mode 0 is the whole search, mode 1 only the diagonals in [kLo, kHi] (no
 * trace kept), mode 2 only the diagonals that can still reach the end
 * within dub edits. Each depth keeps only its live diagonals, as a slice
 * whose first diagonal is recorded beside it. Returns { D, k, trace, klo }
 * or null when it gives up. a and b carry a sentinel each past their end;
 * lineA/lineB are the texts' line arrays and offA/offB the slices' offsets
 * in them, for confirming a hash match with the lines themselves.
 */
function myersSearch(a, b, n, m, lineA, lineB, offA, offB, mode, kLo, kHi, dub, dMax) {
  const target = n - m;
  const keepTrace = mode !== 1;
  const trace = keepTrace ? [] : null;
  const kloOf = keepTrace ? [] : null;
  let kloCur = 0;
  let frontier = new Int32Array(1);
  let x = 0;
  let y = 0;
  while (a[x] === b[y] && lineA[offA + x] === lineB[offB + y]) { x++; y++; }
  frontier[0] = x + 1;
  if (keepTrace) { trace.push(frontier); kloOf.push(0); }
  if (x === n && y === m) return { D: 0, k: 0, trace, kloOf };
  for (let d = 1; d <= dMax; d++) {
    // The diagonals this depth may use.
    let klo = -d;
    let khi = d;
    if (mode === 1) {
      if (klo < kLo) klo = kLo;
      if (khi > kHi) khi = kHi;
    } else if (mode === 2) {
      const lo = target - (dub - d);
      if (klo < lo) klo = lo;
      const hi = target + (dub - d);
      if (khi > hi) khi = hi;
    }
    if (((klo - d) & 1) !== 0) klo++;
    if (((khi - d) & 1) !== 0) khi--;
    const len = klo <= khi ? ((khi - klo) >> 1) + 1 : 0;
    const next = new Int32Array(len);
    if (len > 0) {
      // The previous depth's live slice is indexed by (k - kloCur) / 2.
      // For a new diagonal k, its deletion comes from k - 1 and its
      // insertion from k + 1 on that slice; both indices rise by one as k
      // rises by two, so the insertion's index is carried along.
      const plen = frontier.length;
      let iDown = (klo - 1 - kloCur) >> 1;
      let iUp = (klo + 1 - kloCur) >> 1;
      let down = iDown >= 0 ? frontier[iDown] : 0;
      let up = iUp < plen ? frontier[iUp] : 0;
      for (let t = 0, k = klo; t < len; t++, k += 2) {
        const canDel = down !== 0 && down <= n;
        const canIns = up !== 0 && (up - k - 2) < m;
        if (canDel || canIns) {
          // The deletion's point, or the insertion's, whichever lies further
          // into the old text; the deletion when both reach one point.
          let xx = (canDel && (!canIns || down >= up - 1)) ? down : up - 1;
          let yy = xx - k;
          while (a[xx] === b[yy] && lineA[offA + xx] === lineB[offB + yy]) { xx++; yy++; }
          next[t] = xx + 1;
          if (xx === n && yy === m) return { D: d, k, trace, kloOf };
        }
        down = up;
        iUp++;
        up = iUp < plen ? frontier[iUp] : 0;
      }
    }
    if (keepTrace) { trace.push(next); kloOf.push(klo); }
    frontier = next;
    kloCur = klo;
  }
  return null;
}

/** make.fun's own patch of input.old into input.new. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const oldText = input.old;
  const newText = input.new;

  // Tokenize both texts and hash their lines.
  const oldLines = splitLines(oldText);
  const newLines = splitLines(newText);
  const N = oldLines.length;
  const M = newLines.length;
  const oldHash = new Int32Array(N);
  const newHash = new Int32Array(M);
  for (let i = 0; i < N; i++) oldHash[i] = hashLine(oldLines[i]);
  for (let i = 0; i < M; i++) newHash[i] = hashLine(newLines[i]);

  // The common prefix, then the common suffix of what is left. A hash match
  // is confirmed with the lines themselves, so this is exact.
  let prefix = 0;
  const preMax = N < M ? N : M;
  while (prefix < preMax && oldHash[prefix] === newHash[prefix] && oldLines[prefix] === newLines[prefix]) prefix++;
  let suffix = 0;
  const sufMax = (N - prefix) < (M - prefix) ? (N - prefix) : (M - prefix);
  while (suffix < sufMax && oldHash[N - 1 - suffix] === newHash[M - 1 - suffix] && oldLines[N - 1 - suffix] === newLines[M - 1 - suffix]) suffix++;
  const n = N - prefix - suffix;
  const m = M - prefix - suffix;

  // The middle slices' hashes, each with a sentinel of its own past its end
  // (-1 and -2, which no 31-bit line hash can be), so the snake loop needs
  // no bounds checks: the sentinels never equal each other, nor any line
  // hash, so a snake stops at either end on its own. The string comparison
  // that confirms a hash match therefore only ever runs with both indices
  // inside their slice.
  const a = new Int32Array(n + 1);
  const b = new Int32Array(m + 1);
  a.set(oldHash.subarray(prefix, prefix + n));
  b.set(newHash.subarray(prefix, prefix + m));
  a[n] = -1;
  b[m] = -2;

  // The search: a banded one for an upper bound on the edit distance, then
  // the search pruned to what can still reach the end within that bound.
  // Either search failing falls back to the whole search, which is exact.
  const target = n - m;
  const bandLo = (target < 0 ? target : 0) - BAND;
  const bandHi = (target > 0 ? target : 0) + BAND;
  const banded = myersSearch(a, b, n, m, oldLines, newLines, prefix, prefix, 1, bandLo, bandHi, 0, BAND_CAP);
  let found = null;
  if (banded !== null) found = myersSearch(a, b, n, m, oldLines, newLines, prefix, prefix, 2, 0, 0, banded.D, banded.D);
  if (found === null) found = myersSearch(a, b, n, m, oldLines, newLines, prefix, prefix, 0, 0, 0, 0, n + m);
  if (found === null) throw new Error('makefun-diff: the search ended without reaching both ends');
  const trace = found.trace;
  const kloOf = found.kloOf;
  const D = found.D;
  const kFound = found.k;

  // Walk the trace back from (n, m) to rebuild the edit script's runs, in
  // order: [kind, count] pairs, kind KEEP / DELETE / INSERT.
  const runs = [];
  const pushRun = (kind, count) => {
    if (count <= 0) return;
    const last = runs.length - 2;
    if (last >= 0 && runs[last] === kind) runs[last + 1] += count;
    else runs.push(kind, count);
  };
  {
    // The moves and the snakes after them, recorded backwards.
    const back = [];
    let cx = n;
    let ck = kFound;
    for (let d = D; d >= 1; d--) {
      const prev = trace[d - 1];
      const base = kloOf[d - 1];
      const di = (ck - 1 - base) >> 1;
      const ui = (ck + 1 - base) >> 1;
      const down = (ck - 1 >= -(d - 1) && di >= 0 && di < prev.length) ? prev[di] : 0;
      const up = (ck + 1 <= d - 1 && ui >= 0 && ui < prev.length) ? prev[ui] : 0;
      const canDel = down !== 0 && down <= n;
      const canIns = up !== 0 && (up - ck - 2) < m;
      let del;
      if (canDel && (!canIns || down >= up - 1)) del = true;
      else if (canIns) del = false;
      else throw new Error('makefun-diff: the search ended without reaching both ends');
      let x0;
      let px;
      if (del) {
        x0 = down;
        px = down - 1;
        ck = ck - 1;
      } else {
        x0 = up - 1;
        px = up - 1;
        ck = ck + 1;
      }
      back.push(del ? DELETE : INSERT, cx - x0);
      cx = px;
    }
    // Rebuild forward: the opening snake, then each move and its snake.
    pushRun(KEEP, cx);
    for (let i = back.length - 2; i >= 0; i -= 2) {
      pushRun(back[i], 1);
      pushRun(KEEP, back[i + 1]);
    }
  }
  // The common prefix and suffix, as kept runs around the middle's runs.
  if (suffix > 0) pushRun(KEEP, suffix);
  if (prefix > 0) {
    if (runs.length >= 2 && runs[0] === KEEP) runs[1] += prefix;
    else runs.unshift(KEEP, prefix);
  }

  // The change runs: each a stretch of deletions and insertions between two
  // kept lines, at old line o and new line p.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (let i = 0; i < runs.length; i += 2) {
    const kind = runs[i];
    const count = runs[i + 1];
    if (kind === KEEP) {
      o += count;
      p += count;
      continue;
    }
    let c = changes.length > 0 ? changes[changes.length - 1] : undefined;
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (kind === DELETE) {
      c.dels += count;
      o += count;
      deleted += count;
    } else {
      c.ins += count;
      p += count;
      inserted += count;
    }
  }

  // The hunks: change runs at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks.length > 0 ? hunks[hunks.length - 1] : undefined;
    const prev = h !== undefined ? h[h.length - 1] : undefined;
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }

  // The patch.
  const out = [`${FORMAT} old=${N} new=${M} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  const written = (op, line) => {
    if (line.endsWith('\n')) out.push(op + line);
    else out.push(op + line + '\n%\n');
  };
  for (const h of hunks) {
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = first.o - CONTEXT > 0 ? first.o - CONTEXT : 0;
    const newStart = first.p - (first.o - oldStart);
    const after = N - (last.o + last.dels) < CONTEXT ? N - (last.o + last.dels) : CONTEXT;
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) written('=', oldLines[at]);
      for (let i = 0; i < c.dels; i++) written('-', oldLines[c.o + i]);
      for (let i = 0; i < c.ins; i++) written('+', newLines[c.p + i]);
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) written('=', oldLines[at]);
  }
  return out.join('');
}
