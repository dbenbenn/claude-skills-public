#!/usr/bin/env python3
"""Concatenate a mission's shared modules into one self-contained prove2.me solution file.

usage: merge.py OUT MODULE [MODULE ...]

A solution may import only the mission's definitions, so a development shared across
submissions is kept as modules (`Solutions/*.lean`, importing each other) and concatenated per
submission. Import lines are dropped and one header is prefixed: the union of the modules' own
non-`Solutions.` imports. A declaration that appears in more than one module is dropped from the
later module, by BARE name -- so two modules must not reuse a name in different namespaces.
Any `namespace`/`end`/`open`/`section` line inside a dropped block is kept: dropping one once
deleted a file's closing `end`, the merged file compiled locally with `solution` silently
namespaced, and the verifier answered "Unknown identifier solution" four times. The script now
refuses to write a file whose namespace/end counts differ or that holds more than one
`theorem solution`; append the `solution` tail AFTER merging.
"""
import re, sys

def header(mods):
    """The merged file's imports: every non-`Solutions.` import any module makes, first-seen
    order, so the header is derived from the modules rather than hard-coded per mission."""
    seen, out = set(), []
    for mod in mods:
        for ln in open(mod).read().split('\n'):
            if ln.startswith('import ') and not ln.startswith('import Solutions.') and ln not in seen:
                seen.add(ln); out.append(ln)
    return '\n'.join(out) + '\n'

DECL = re.compile(r'^(?:@\[simp\] )?(?:noncomputable )?(?:lemma|theorem|def|abbrev) ([^\s:({]+)')


def blocks(text):
    """Split into (name-or-None, text) chunks at top-level declarations."""
    lines = text.split('\n')
    out, cur, name = [], [], None
    i = 0
    while i < len(lines):
        ln = lines[i]
        m = DECL.match(ln)
        if m:
            # attach a directly preceding docstring
            doc = []
            while cur and (cur[-1].startswith('/--') or (doc and not cur[-1].startswith('/--'))):
                doc.insert(0, cur.pop())
                if doc[0].startswith('/--'):
                    break
            if cur:
                out.append((name, '\n'.join(cur)))
            cur, name = doc + [ln], m.group(1)
        else:
            cur.append(ln)
        i += 1
    if cur:
        out.append((name, '\n'.join(cur)))
    return out


def main():
    out_path, mods = sys.argv[1], sys.argv[2:]
    seen = set()
    pieces = [header(mods)]
    for mod in mods:
        body = [ln for ln in open(mod).read().split('\n') if not ln.startswith('import ')]
        kept = []
        for name, chunk in blocks('\n'.join(body)):
            if name is not None:
                if name in seen:
                    sys.stderr.write(f'dropping duplicate {name} from {mod}\n')
                    # a chunk runs to the next declaration, so it may carry the module's
                    # closing `end` (or a stray `namespace`/`open`): keep those lines
                    structural = [ln for ln in chunk.split('\n')
                                  if re.match(r'^(end|namespace|open|section)\b', ln)]
                    if structural:
                        kept.append('\n'.join(structural))
                    continue
                seen.add(name)
            kept.append(chunk)
        pieces.append('\n'.join(kept).strip() + '\n')
    merged = '\n'.join(pieces)
    # `section` (named or anonymous) opens a scope exactly as `namespace` does, and a bare `end`
    # closes an anonymous section; count both, or a module with a `section` is refused.
    n_ns = sum(1 for ln in merged.split('\n') if re.match(r'^(namespace\s|section\b)', ln))
    n_end = sum(1 for ln in merged.split('\n') if re.match(r'^end\b', ln))
    if n_ns != n_end:
        sys.exit(f'refusing: {n_ns} namespace/section lines but {n_end} end lines -- a trailing '
                 '`theorem solution` would be namespaced and invisible to the verifier')
    solution_count = sum(1 for ln in merged.split('\n') if ln.startswith('theorem solution'))
    if solution_count > 0:
        sys.exit(f'refusing: {solution_count} `theorem solution` already in the modules; '
                 'strip it (the verifier takes the FIRST one)')
    open(out_path, 'w').write(merged)
    print('lines:', merged.count('\n'))


main()
