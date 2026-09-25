#!/usr/bin/env python3
"""Concatenate a mission's shared modules into one self-contained prove2.me solution file.

usage: merge.py OUT MODULE [MODULE ...]

A solution may import only the mission's definitions, so a development shared across
submissions is kept as modules (`Solutions/*.lean`, importing each other) and concatenated per
submission. Import lines are dropped and one header is prefixed: the union of the modules' own
non-`Solutions.` imports. A declaration that appears in more than one module with identical
text is dropped from the later module; one whose name matches an earlier declaration but whose
text differs is refused, since keeping either would rebind the other's uses. Names are compared
as written, so two modules must not reuse a name in different namespaces. Only the declaration's
own span is ever dropped (see blocks()): dropping more once deleted a file's closing `end`, the merged file compiled locally with `solution` silently
namespaced, and the verifier answered "Unknown identifier solution" four times. The script now
refuses to write a file whose namespace/end counts differ or that holds more than one
`theorem solution`; append the `solution` tail AFTER merging.
"""
import os, re, sys

def header(mods):
    """The merged file's imports: every non-`Solutions.` import any module makes, first-seen
    order, so the header is derived from the modules rather than hard-coded per mission."""
    seen, out = set(), []
    for mod in mods:
        for ln in open(mod).read().split('\n'):
            if ln.startswith('import ') and not ln.startswith('import Solutions.') and ln not in seen:
                seen.add(ln); out.append(ln)
    return '\n'.join(out) + '\n'

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prune_solution import parse


def blocks(text):
    """Split into (name-or-None, text) chunks: each declaration's own span, as prune_solution
    parses it (attributes, a docstring and a `set_option … in` above it included, its body, up to
    the next top-level command), and between them unnamed chunks holding everything else --
    `namespace`, `end`, `open`, `variable`, `notation` and the like.

    Only a named chunk can be dropped as a duplicate, so dropping one can no longer take a
    following `@[simp]`, docstring, `variable` or closing `end` with it: an earlier version ran
    each chunk to the next declaration it recognised, and a dropped duplicate silently stripped
    the `@[simp]` off the lemma after it."""
    lines = text.split('\n')
    out, cur = [], 0
    for name, _kind, st, en, _attr in sorted(parse(lines), key=lambda d: d[2]):
        # spans must not overlap; if parse ever returns one that does, emitting it whole
        # duplicates the overlap (it once doubled a run of one-line `@[simp]` lemmas)
        st = max(st, cur)
        if en <= st:
            continue
        if st > cur:
            out.append((None, '\n'.join(lines[cur:st])))
        out.append((name, '\n'.join(lines[st:en])))
        cur = en
    if cur < len(lines):
        out.append((None, '\n'.join(lines[cur:])))
    return out


def main():
    out_path, mods = sys.argv[1], sys.argv[2:]
    seen = {}  # name -> the declaration's own text, to tell a true duplicate from a clash
    pieces = [header(mods)]
    for mod in mods:
        body = [ln for ln in open(mod).read().split('\n') if not ln.startswith('import ')]
        kept = []
        for name, chunk in blocks('\n'.join(body)):
            if name is not None:
                decl = chunk.strip()
                if name in seen and seen[name] != decl:
                    # same bare name, different declaration (e.g. two provers' helpers named
                    # `ev` in different namespaces): keeping the first would silently
                    # rebind the second module's uses to the wrong definition
                    sys.exit(f'refusing: {name} in {mod} differs from an earlier declaration '
                             'of the same name -- rename one, or give each module its own '
                             'namespace and concatenate instead')
                if name in seen:
                    sys.stderr.write(f'dropping duplicate {name} from {mod}\n')
                    continue
                seen[name] = decl
            kept.append(chunk)
        pieces.append('\n'.join(kept).strip() + '\n')
    merged = '\n'.join(pieces)
    # `universe` lines are not declarations, so the name dedup above never sees them, and Lean
    # refuses a level declared twice. Two modules writing `universe u v` and `universe u` collide
    # even though neither line repeats. Keep each level once, in first-seen order.
    # A scoped `universe u in` declares its levels for the next command only: drop the levels
    # already in scope (dropping the whole line if none remain, never leaving a bare
    # `universe in`), and do not record the scoped levels as declared for the rest of the file.
    seen_lvl, out_lines = [], []
    for ln in merged.split('\n'):
        m = re.match(r'^universe\s+(.+?)(\s+in)?\s*$', ln)
        if not m:
            out_lines.append(ln); continue
        fresh = [u for u in m.group(1).split() if u not in seen_lvl]
        if m.group(2):
            if fresh:
                out_lines.append('universe ' + ' '.join(fresh) + ' in')
            continue
        seen_lvl += fresh
        if fresh:
            out_lines.append('universe ' + ' '.join(fresh))
    merged = '\n'.join(out_lines)
    # `section` (named, anonymous or `noncomputable`) and `mutual` open a block closed by `end`
    # exactly as `namespace` does; count them all, or a module using one is refused.
    n_ns = sum(1 for ln in merged.split('\n')
               if re.match(r'^(namespace\s|(noncomputable\s+)?section\b|mutual\b)', ln))
    n_end = sum(1 for ln in merged.split('\n') if re.match(r'^end\b', ln))
    if n_ns != n_end:
        sys.exit(f'refusing: {n_ns} namespace/section lines but {n_end} end lines -- a trailing '
                 '`theorem solution` would be namespaced and invisible to the verifier')
    solution_count = sum(1 for ln in merged.split('\n') if re.match(r'^theorem\s+solution\b', ln))
    if solution_count > 0:
        sys.exit(f'refusing: {solution_count} `theorem solution` already in the modules; '
                 'strip it (the verifier takes the FIRST one)')
    open(out_path, 'w').write(merged)
    print('lines:', merged.count('\n'))


main()
