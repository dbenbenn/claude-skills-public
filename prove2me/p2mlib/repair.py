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
    lines = error_lines(output) if isinstance(output, str) else \
        [int(m.group(1)) for o in output for m in [ERROR.match(o)] if m]
    if not lines:
        return None
    cmds = _commands(text)
    cut = []
    for ln in lines:
        hit = next((c for c in cmds if c[0] <= ln <= c[1]), None)
        if hit is None or not _is_context(hit[2]):
            return None
        if hit[2] not in cut:
            cut.append(hit[2])
    new, applied, _ = apply_cuts(text, cut)
    return new, applied


def apply_cuts(text, cuts):
    applied, stale = [], []
    for c in cuts:
        pat = re.compile(r'(^|\n)' + re.escape(c) + r'\n(\n?)')
        if pat.search(text):
            text = pat.sub(lambda m: m.group(1), text, count=1)
            applied.append(c)
        else:
            stale.append(c)
    return text, applied, stale
