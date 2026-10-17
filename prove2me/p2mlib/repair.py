"""Cut a context command Lean rejects from a carved file, and nothing else.

A carved file keeps or drops each context command (`variable`, `local notation`, `open`,
`include`, `omit`, `attribute [local …]`) by reading source text, and each sharpened rule exposed
the edge of another (Erdős 3 v2, 2026-10-16/17: a notation kept for a one-letter token match whose
variables were rightly dropped, a variable needing an instance nothing kept brought in, …). Lean's
error points at the exact line. A context command that does not elaborate cannot be what a kept
declaration needs (if it were, that declaration fails next, and an error inside a declaration is
never repaired), so cutting it is safe.

* `error_lines(compiler_output)` -> line numbers of the errors.
* `repair(text, compiler_output_lines)` -> (new text, [cut command texts]), or None when any error
  is outside a context command (a person looks).
* `apply_cuts(text, cuts)` -> (new text, applied, stale): recorded cuts re-applied after the file
  is generated again, each only where its exact text still stands as a command.
"""
import re

ERROR = re.compile(r'^\S*?:(\d+):(\d+): error\b', re.M)
CONTEXT = re.compile(r'(?:variable|include|omit|open|local\s+(?:notation3?|infixl?|infixr|prefix|postfix)|'
                     r'attribute\s*\[\s*local\b)')
STARTS = re.compile(r'^(?:/--|@\[|[A-Za-z_#])')


def error_lines(output):
    return [int(m.group(1)) for m in ERROR.finditer(output)]


def _errors(output):
    """[(line, column)] of the errors (Lean columns count code points, as Python strings do)."""
    if isinstance(output, str):
        return [(int(m.group(1)), int(m.group(2))) for m in ERROR.finditer(output)]
    return [(int(m.group(1)), int(m.group(2))) for o in output for m in [ERROR.match(o)] if m]


OPEN, CLOSE = '([{⦃', ')]}⦄'


def _groups(cmd):
    """[(start, end)] of the top-level binder groups of a `variable` command's text."""
    out, depth, start = [], 0, None
    for i, ch in enumerate(cmd):
        if ch in OPEN:
            if depth == 0:
                start = i
            depth += 1
        elif ch in CLOSE and depth:
            depth -= 1
            if depth == 0:
                out.append((start, i + 1))
    return out


def _without(cmd, a, b):
    """cmd without cmd[a:b] and the blanks it leaves (a line left empty goes)."""
    left, right = cmd[:a].rstrip(' '), cmd[b:].lstrip(' ')
    if left.endswith('\n') and (right.startswith('\n') or not right):
        left = left[:-1]
    elif not left.endswith('\n') and not right.startswith('\n') and right:
        left += ' '
    return left + right


def _commands(text):
    """[(first line, last line, text)] of the top-level commands: a command starts at column 0 and
    runs until the next line that starts one (blank lines end it too)."""
    lines = text.split('\n')
    out, cur = [], None
    for i, l in enumerate(lines, 1):
        if l and not l[0].isspace() and STARTS.match(l):
            if cur:
                out.append(cur)
            cur = [i, i]
        elif cur and l.strip():
            cur[1] = i                                   # a continuation line
        elif cur:
            out.append(cur)
            cur = None
    if cur:
        out.append(cur)
    return [(a, b, '\n'.join(lines[a - 1:b])) for a, b in out]


def _is_context(cmd):
    return bool(CONTEXT.match(cmd)) and not cmd.startswith('scoped[')


def repair(text, output):
    errs = _errors(output)
    if not errs:
        return None
    cmds = _commands(text)
    whole, parts = [], []                 # whole commands; (command text, group text) to cut
    for ln, col in errs:
        hit = next((c for c in cmds if c[0] <= ln <= c[1]), None)
        if hit is None or not _is_context(hit[2]):
            return None
        a, _, cmd = hit
        if cmd.startswith('variable'):
            lines = cmd.split('\n')
            off = sum(len(l) + 1 for l in lines[:ln - a]) + col
            gs = _groups(cmd)
            g = next(((x, y) for x, y in gs if x <= off < y), None)
            if g and len(gs) > 1:
                if (cmd, cmd[g[0]:g[1]]) not in parts:
                    parts.append((cmd, cmd[g[0]:g[1]]))
                continue
        if cmd not in whole:
            whole.append(cmd)
    cut = list(whole) + [grp for cmd, grp in parts if cmd not in whole]
    new, applied, _ = apply_cuts(text, cut)
    return new, applied


def apply_cuts(text, cuts):
    """Re-apply recorded cuts: a whole command where its exact text stands as a command, a binder
    group (text starting with a bracket) where it stands as a group of a `variable` command."""
    applied, stale = [], []
    for c in cuts:
        pat = re.compile(r'(^|\n)' + re.escape(c) + r'\n(\n?)')
        if pat.search(text):
            text = pat.sub(lambda m: m.group(1), text, count=1)
            applied.append(c)
            continue
        done = False
        if c[:1] in OPEN:
            for a, b, cmd in _commands(text):
                if not cmd.startswith('variable'):
                    continue
                g = next(((x, y) for x, y in _groups(cmd) if cmd[x:y] == c), None)
                if g:
                    new_cmd = _without(cmd, *g)
                    i = text.index(cmd)
                    text = text[:i] + new_cmd + text[i + len(cmd):]
                    done = True
                    break
        (applied if done else stale).append(c)
    return text, applied, stale
