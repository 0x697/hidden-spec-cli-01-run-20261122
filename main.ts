// mend: applies AI-written edits in four formats to a tree of text files.
// Node 22, the standard library alone; run as `node main.ts [options] [PATCH]`.
// Implements SPEC.md sections 1-10: the command line, output and exit codes,
// safe paths, format detection, three-tier line matching, unified diffs,
// SEARCH/REPLACE blocks, V4A patches, JSON edits and all-or-nothing writes.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and
// this file hands over to runner.ts (the last lines below): keep that hand-over
// and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file as lines: its line break, its lines, whether it ends with one. */
interface FileText {
  lines: string[];
  br: '\r\n' | '\n';
  final: boolean;
}

function splitText(text: string): FileText {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br: '\r\n' | '\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { lines, br, final };
}

function joinText(f: FileText): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** Successful move edits: new path -> old path, for the `R` output lines. */
let moves = new Map<string, string>();

function recordMove(oldP: string, newP: string): void {
  const orig = moves.get(oldP);
  if (orig !== undefined) {
    moves.delete(oldP);
    moves.set(newP, orig);
  } else {
    moves.set(newP, oldP);
  }
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---- matching (SPEC.md section 5) ----

const rtrimWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadingWs = (s: string): string => /^[ \t]*/.exec(s)?.[0] ?? '';

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rtrimWs(a) === rtrimWs(b);
  return trimWs(a) === trimWs(b);
}

/** Every 0-based position where O occurs in lines at this tier; occurrences may overlap. */
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0 || o.length > lines.length) return out;
  for (let i = 0; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let k = 0; k < o.length; k++) {
      if (!lineEq(lines[i + k]!, o[k]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which O occurs, with its positions; null when it occurs at no tier. */
function findTier(lines: string[], o: string[], strict: boolean): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const positions = occurrences(lines, o, t);
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

/** One line of N: a context line (written as the file's own matched line) or a new line. */
interface NewLine {
  text: string;
  ctx: number | null;
}

/** Resolve N against the file's matched lines: context lines are the file's own; at tier 2 the rest are re-indented. */
function resolveNew(fileLines: string[], o: string[], n: NewLine[], tier: number, pos: number): string[] {
  const f = tier === 2 && o.length > 0 ? leadingWs(fileLines[pos]!) : '';
  const p = tier === 2 && o.length > 0 ? leadingWs(o[0]!) : '';
  return n.map((item) => {
    if (item.ctx !== null) return fileLines[pos + item.ctx]!;
    const t = item.text;
    if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(p)) return f + t.slice(p.length);
    return t;
  });
}

/** Split O/N out of a body of context/`-`/`+` lines (a unified hunk or a V4A chunk). */
function splitBody(body: { kind: string; text: string }[]): { o: string[]; n: NewLine[] } {
  const o: string[] = [];
  const n: NewLine[] = [];
  for (const b of body) {
    if (b.kind === ' ') {
      o.push(b.text);
      n.push({ text: b.text, ctx: o.length - 1 });
    } else if (b.kind === '-') {
      o.push(b.text);
    } else if (b.kind === '+') {
      n.push({ text: b.text, ctx: null });
    }
  }
  return { o, n };
}

/** A file created by an edit: its lines, LF breaks, ended by a line break (none when it has no lines). */
function createdText(lines: string[]): string {
  return lines.length === 0 ? '' : `${lines.join('\n')}\n`;
}

// ---- JSON edits (SPEC.md section 9) ----

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- unified diffs (SPEC.md section 6) ----

interface HunkLine {
  kind: ' ' | '-' | '+' | '\\';
  text: string;
}
interface Hunk {
  a: number;
  body: HunkLine[];
}
interface Section {
  oldPath: string | null;
  newPath: string | null;
  namedOld: boolean;
  namedNew: boolean;
  gitOld: string | null;
  gitNew: string | null;
  isNew: boolean;
  isDel: boolean;
  hunks: Hunk[];
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const GIT_RE = /^diff --git a\/(\S+) b\/(\S+)$/;

/** A `--- ` / `+++ ` path: up to the first tab, surrounding spaces removed, `a/`/`b/` stripped; `/dev/null` is no file. */
function headerPath(line: string): string | null {
  const raw = line.slice(4).split('\t')[0]!.trim();
  if (raw === '/dev/null') return null;
  if (raw.startsWith('a/')) return raw.slice(2);
  if (raw.startsWith('b/')) return raw.slice(2);
  return raw;
}

function parseUnified(lines: string[]): Section[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let curHunk: Hunk | null = null;
  let headerDone = false;
  let hasPair = false;
  const endBody = (): void => {
    if (curHunk !== null) {
      while (curHunk.body.length > 0 && curHunk.body[curHunk.body.length - 1]!.kind === ' ' && curHunk.body[curHunk.body.length - 1]!.text === '') curHunk.body.pop();
      curHunk = null;
    }
  };
  const newSection = (oldP: string | null, newP: string | null): Section => {
    endBody();
    const s: Section = { oldPath: oldP, newPath: newP, namedOld: false, namedNew: false, gitOld: null, gitNew: null, isNew: false, isDel: false, hunks: [] };
    sections.push(s);
    cur = s;
    headerDone = false;
    hasPair = false;
    return s;
  };
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (curHunk !== null) {
      if (line.startsWith('diff --git ') || (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ '))) {
        endBody();
        continue;
      }
      const c = line[0];
      if (c === ' ' || c === '-' || c === '+' || c === '\\' || line === '') {
        curHunk.body.push({ kind: (line === '' ? ' ' : c) as HunkLine['kind'], text: line === '' ? '' : line.slice(1) });
        i++;
        continue;
      }
      endBody();
      continue;
    }
    if (line.startsWith('diff --git ')) {
      const m = GIT_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const s = newSection(null, null);
      s.gitOld = m[1] === '/dev/null' ? null : m[1]!;
      s.gitNew = m[2] === '/dev/null' ? null : m[2]!;
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      const m = HUNK_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      curHunk = { a: Number(m[1]), body: [] };
      cur.hunks.push(curHunk);
      headerDone = true;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && !headerDone && !hasPair) {
        cur.oldPath = headerPath(line);
        cur.newPath = headerPath(lines[i + 1]!);
        cur.namedOld = true;
        cur.namedNew = true;
        hasPair = true;
      } else {
        const s = newSection(null, null);
        s.oldPath = headerPath(line);
        s.newPath = headerPath(lines[i + 1]!);
        s.namedOld = true;
        s.namedNew = true;
        hasPair = true;
      }
      i += 2;
      continue;
    }
    if (cur !== null && !headerDone) {
      if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (line.startsWith('+++ ')) {
        cur.newPath = headerPath(line);
        cur.namedNew = true;
        hasPair = true;
        i++;
        continue;
      }
      if (line.startsWith('rename from ')) {
        cur.oldPath = line.slice('rename from '.length).trim();
        cur.namedOld = true;
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.newPath = line.slice('rename to '.length).trim();
        cur.namedNew = true;
        i++;
        continue;
      }
      if (line === 'new file mode' || line.startsWith('new file mode ')) {
        cur.isNew = true;
        i++;
        continue;
      }
      if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) {
        cur.isDel = true;
        i++;
        continue;
      }
      i++;
      continue;
    }
    i++;
  }
  endBody();
  return sections;
}

/** Apply one hunk to a file; returns the new file and the hunk's length delta (for the next hunk's `d`). */
function applyHunk(f: FileText, hunk: Hunk, strict: boolean, d: number): { file: FileText; delta: number } {
  const body = hunk.body;
  const { o, n } = splitBody(body);
  const lines = f.lines;
  const out: FileText = { lines: [...lines], br: f.br, final: f.final };
  if (o.length === 0) {
    if (n.length === 0) return { file: out, delta: 0 };
    const at = Math.min(Math.max(hunk.a + d, 0), lines.length);
    const resolved = n.map((item) => item.text);
    out.lines.splice(at, 0, ...resolved);
    if (at === lines.length) {
      const lastPlus = [...body].reverse().find((b) => b.kind === '+' || b.kind === ' ');
      const idx = lastPlus === undefined ? -1 : body.lastIndexOf(lastPlus);
      const noBreak = idx >= 0 && body[idx + 1]?.kind === '\\';
      out.final = !noBreak;
    }
    return { file: out, delta: n.length };
  }
  const found = findTier(lines, o, strict);
  if (found === null) throw new Fail('no-match', '');
  const target = hunk.a - 1 + d;
  let best = found.positions[0]!;
  for (const pos of found.positions) {
    if (Math.abs(pos - target) < Math.abs(best - target)) best = pos;
  }
  const pos = best;
  const resolved = resolveNew(lines, o, n, found.tier, pos);
  out.lines.splice(pos, o.length, ...resolved);
  if (pos + o.length === lines.length) {
    let lastIdx = -1;
    for (let k = body.length - 1; k >= 0; k--) {
      if (body[k]!.kind === ' ' || body[k]!.kind === '+') {
        lastIdx = k;
        break;
      }
    }
    const noBreak = lastIdx >= 0 && body[lastIdx + 1]?.kind === '\\';
    out.final = !noBreak;
  }
  return { file: out, delta: n.length - o.length };
}

function unifiedEdit(sec: Section, strict: boolean): Edit {
  return (tree) => {
    // Paths: the `---`/`+++` pair or `rename` lines name them; the `diff --git` paths are the fallback.
    // A path named as `/dev/null` is explicitly no file, so it never falls back to the git paths.
    const oldP = sec.namedOld ? sec.oldPath : sec.gitOld;
    const newP = sec.namedNew ? sec.newPath : sec.gitNew;
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    const isCreate = sec.isNew || oldP === null;
    const isDelete = !isCreate && (sec.isDel || newP === null);
    if (isCreate) {
      if (newP === null) throw new Fail('unsafe', '');
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const plus: string[] = [];
      for (const h of sec.hunks) {
        for (const b of h.body) {
          if (b.kind === '+') plus.push(b.text);
        }
      }
      let text = createdText(plus);
      if (plus.length > 0) {
        let lastPlus = -1;
        let lastPlusHunk: Hunk | null = null;
        for (const h of sec.hunks) {
          for (let k = 0; k < h.body.length; k++) {
            if (h.body[k]!.kind === '+') {
              lastPlus = k;
              lastPlusHunk = h;
            }
          }
        }
        if (lastPlusHunk !== null && lastPlusHunk.body[lastPlus + 1]?.kind === '\\') text = plus.join('\n');
      }
      tree.now.set(newP, text);
      return;
    }
    if (isDelete) {
      if (oldP === null) throw new Fail('unsafe', '');
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (oldP === null || newP === null) throw new Fail('unsafe', '');
    const cur = tree.get(oldP);
    if (cur === null) throw new Fail('missing', oldP);
    const isMove = oldP !== newP;
    if (isMove && tree.get(newP) !== null) throw new Fail('exists', newP);
    let f = splitText(cur);
    let d = 0;
    try {
      for (const h of sec.hunks) {
        const r = applyHunk(f, h, strict, d);
        f = r.file;
        d += r.delta;
      }
    } catch (e) {
      if (e instanceof Fail && e.path === '') throw new Fail(e.code, oldP);
      throw e;
    }
    const text = joinText(f);
    if (isMove) {
      tree.now.set(oldP, null);
      tree.now.set(newP, text);
      recordMove(oldP, newP);
    } else {
      tree.now.set(oldP, text);
    }
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections = parseUnified(lines);
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => unifiedEdit(s, strict));
}

// ---- SEARCH/REPLACE blocks (SPEC.md section 7) ----

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, createdText(newLines));
      return;
    }
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    const f = splitText(cur);
    const found = findTier(f.lines, oldLines, strict);
    if (found === null) throw new Fail('no-match', path);
    if (found.positions.length > 1) throw new Fail('ambiguous', path);
    const pos = found.positions[0]!;
    const resolved = resolveNew(f.lines, oldLines, newLines.map((t) => ({ text: t, ctx: null })), found.tier, pos);
    f.lines.splice(pos, oldLines.length, ...resolved);
    tree.now.set(path, joinText(f));
  };
}

function srEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let j = searchLine - 1; j >= prevEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = searchLine + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq === -1) throw new Exit2(`error: parse ${searchLine + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep === -1) throw new Exit2(`error: parse ${searchLine + 1}`);
    edits.push(srEdit(path, lines.slice(searchLine + 1, eq), lines.slice(eq + 1, rep), strict));
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

// ---- V4A patches (SPEC.md section 8) ----

interface V4aChunk {
  anchor: string | null;
  eof: boolean;
  body: { kind: ' ' | '-' | '+' | '\\'; text: string }[];
}
interface V4aSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  lines: string[];
  chunks: V4aChunk[];
  updateLine: number;
}

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last > first && blank(lines[last]!)) last--;
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: V4aSection[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    let kind: V4aSection['kind'] | null = null;
    let path = '';
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      path = line.slice('*** Add File: '.length).trim();
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'delete';
      path = line.slice('*** Delete File: '.length).trim();
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'update';
      path = line.slice('*** Update File: '.length).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const sec: V4aSection = { kind, path, moveTo: null, lines: [], chunks: [], updateLine: i + 1 };
    sections.push(sec);
    i++;
    while (i < last) {
      const l = lines[i]!;
      if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ')) break;
      sec.lines.push(l);
      i++;
    }
    while (sec.lines.length > 0 && blank(sec.lines[sec.lines.length - 1]!)) sec.lines.pop();
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  for (const sec of sections) {
    if (sec.kind === 'add') {
      const fileLines: string[] = [];
      for (let k = 0; k < sec.lines.length; k++) {
        const l = sec.lines[k]!;
        if (l === '') fileLines.push('');
        else if (l.startsWith('+')) fileLines.push(l.slice(1));
        else throw new Exit2(`error: parse ${sec.updateLine + 1 + k}`);
      }
      const path = sec.path;
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, createdText(fileLines));
      });
      continue;
    }
    if (sec.kind === 'delete') {
      for (let k = 0; k < sec.lines.length; k++) {
        if (!blank(sec.lines[k]!)) throw new Exit2(`error: parse ${sec.updateLine + 1 + k}`);
      }
      const path = sec.path;
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.now.set(path, null);
      });
      continue;
    }
    // Update: optional `*** Move to:` first, then chunks.
    let at = 0;
    while (at < sec.lines.length && blank(sec.lines[at]!)) at++;
    if (at < sec.lines.length && sec.lines[at]!.startsWith('*** Move to: ')) {
      sec.moveTo = sec.lines[at]!.slice('*** Move to: '.length).trim();
      at++;
    }
    let cur: V4aChunk | null = null;
    const startChunk = (anchor: string | null): void => {
      cur = { anchor, eof: false, body: [] };
      sec.chunks.push(cur);
    };
    for (let k = at; k < sec.lines.length; k++) {
      const l = sec.lines[k]!;
      if (l.startsWith('@@')) {
        startChunk(l.slice(2).trim());
        continue;
      }
      if (l === '*** End of File') {
        if (cur !== null) {
          cur.eof = true;
          cur = null;
        }
        continue;
      }
      if (l.startsWith('*** ')) throw new Exit2(`error: parse ${sec.updateLine + 1 + k}`);
      const c = l[0];
      if (c === ' ' || c === '-' || c === '+' || l === '') {
        if (cur === null) {
          if (sec.chunks.length > 0) throw new Exit2(`error: parse ${sec.updateLine + 1 + k}`);
          startChunk(null);
        }
        cur!.body.push({ kind: (l === '' ? ' ' : c) as V4aChunk['body'][number]['kind'], text: l === '' ? '' : l.slice(1) });
        continue;
      }
      throw new Exit2(`error: parse ${sec.updateLine + 1 + k}`);
    }
    if (sec.chunks.length === 0 && sec.moveTo === null) throw new Exit2(`error: parse ${sec.updateLine}`);
    edits.push(v4aUpdateEdit(sec, strict));
  }
  return edits;
}

/** The first line at or after `cursor` equal to the anchor, at the first tier with one; -1 when there is none. */
function findAnchor(lines: string[], anchor: string, cursor: number, strict: boolean): number {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let i = cursor; i < lines.length; i++) {
      if (lineEq(lines[i]!, anchor, t)) return i;
    }
  }
  return -1;
}

function v4aUpdateEdit(sec: V4aSection, strict: boolean): Edit {
  const path = sec.path;
  const moveTo = sec.moveTo;
  const chunks = sec.chunks;
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    let f = splitText(cur);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== null) {
        const idx = findAnchor(f.lines, chunk.anchor, cursor, strict);
        if (idx === -1) throw new Fail('no-match', path);
        cursor = idx + 1;
      }
      const { o, n } = splitBody(chunk.body);
      if (o.length === 0) {
        const at = chunk.eof ? f.lines.length : cursor;
        const resolved = n.map((item) => item.text);
        f.lines.splice(at, 0, ...resolved);
        cursor = at + resolved.length;
        continue;
      }
      const found = findTier(f.lines, o, strict);
      if (found === null) throw new Fail('no-match', path);
      let pos = -1;
      for (const p of found.positions) {
        if (p < cursor) continue;
        if (chunk.eof && p + o.length !== f.lines.length) continue;
        pos = p;
        break;
      }
      if (pos === -1) throw new Fail('no-match', path);
      const resolved = resolveNew(f.lines, o, n, found.tier, pos);
      f.lines.splice(pos, o.length, ...resolved);
      cursor = pos + resolved.length;
    }
    const text = joinText(f);
    if (moveTo !== null) {
      tree.now.set(path, null);
      tree.now.set(moveTo, text);
      recordMove(path, moveTo);
    } else {
      tree.now.set(path, text);
    }
  };
}

// ---- invocation (SPEC.md sections 1, 2 and 10) ----

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = srEdits(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  moves = new Map();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const beforeMoves = new Map(moves);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      moves = beforeMoves;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: { key: string; line: string }[] = [];
  const handled = new Set<string>();
  for (const [nw, old] of moves) {
    if (tree.original(old) !== null && tree.get(old) === null && tree.original(nw) === null && tree.get(nw) !== null) {
      rows.push({ key: nw, line: `R ${old} -> ${nw}` });
      handled.add(old);
      handled.add(nw);
    }
  }
  for (const p of [...tree.now.keys()]) {
    if (handled.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const out = rows.map((r) => r.line);
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
