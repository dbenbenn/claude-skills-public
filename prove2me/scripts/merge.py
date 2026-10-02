#!/usr/bin/env python3
"""Concatenate a mission's shared modules into one self-contained prove2.me solution file.

usage: merge.py OUT MODULE [MODULE ...]

A solution may import only the mission's definitions, so a development shared across
submissions is kept as modules (`Solutions/*.lean`, importing each other) and concatenated per
submission. Each module's import header is dropped and one header is prefixed: the union of the
modules' own non-`Solutions.` imports. Each module becomes its own `section ... end`, so its
`open`s stay file-scoped as they were (Monod 2026-09-30: an `open ... Matrix` in one module made
`zpow_add` ambiguous in the next), and a scope it leaves open at end of file (a trailing
`noncomputable section`) is closed before the wrapper's `end`.

A declaration that appears in more than one module with identical text is dropped from the later
module; one whose name matches an earlier declaration but whose text differs is refused, since
keeping either would rebind the other's uses. A file already holding a `theorem solution` is
refused (the verifier takes the FIRST one); append the `solution` tail AFTER merging.

How: the modules are concatenated as they are (each in its section) and Lean parses that once
(LeanInfo, parse-only: the dev modules need not be built, and notation a module declares is
elaborated before the next one is parsed). Declarations are then compared by the full names Lean
gives them -- `S6.W` and `S6.CoxA.W` are different (they were refused while names were compared as
written) -- and only whole commands are removed, so dropping a duplicate can never take the next
lemma's `@[simp]`, a docstring, a `variable` or a closing `end` with it (each happened under the
earlier line-based splitter: the last one namespaced `solution` and the verifier answered
"Unknown identifier solution" four times).

`universe` levels are declared once, after the header: Lean refuses a level declared twice, and two
modules writing `universe u v` and `universe u` collide.
"""
import os
import re
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))  # p2mlib
from p2mlib import leanedit, leaninfo  # noqa: E402
from p2mlib.leantext import header_end, strip  # noqa: E402


def header(texts):
    """The merged file's imports: every non-`Solutions.` import any module makes, first-seen
    order, so the header is derived from the modules rather than hard-coded per mission."""
    seen = []
    for t in texts:
        for m in re.findall(r'^import\s+(\S+)', strip(t[:header_end(t)]), re.M):
            if not m.startswith('Solutions.') and m not in seen:
                seen.append(m)
    return ''.join('import %s\n' % m for m in seen)


def _universes(regions):
    """Declare every unscoped universe level once: (levels, regions without their `universe`
    lines). A scoped `universe u in` declares for the next command only: it loses the levels
    already declared (and the line, if none remain; never a bare `universe in`)."""
    lvls = []
    for r in regions:
        for ln in r.split('\n'):
            m = re.match(r'^universe\s+(.+?)\s*$', ln)
            if m and not m.group(1).endswith(' in') and m.group(1) != 'in':
                lvls += [u for u in m.group(1).split() if u not in lvls]
    out = []
    for r in regions:
        lines = []
        for ln in r.split('\n'):
            m = re.match(r'^universe\s+(.+?)(\s+in)?\s*$', ln)
            if not m:
                lines.append(ln)
            elif m.group(2):
                fresh = [u for u in m.group(1).split() if u not in lvls]
                if fresh:
                    lines.append('universe ' + ' '.join(fresh) + ' in')
        out.append('\n'.join(lines))
    return lvls, out


def merge(mods, scratch=None):
    """(merged text, byte offset of each module's `section` in it). Exits 'refusing: ...'."""
    texts = [open(m, encoding='utf-8').read() for m in mods]
    hdr = header(texts)
    naive, spans = hdr, []
    for t in texts:
        naive += 'section\n'
        a = len(naive.encode())
        naive += t[header_end(t):].rstrip('\n') + '\n'
        spans.append((a, len(naive.encode())))
        naive += 'end\n'
    fd, tmp = tempfile.mkstemp(suffix='.lean', prefix='.merge_', dir=scratch)
    with os.fdopen(fd, 'w', encoding='utf-8') as f:
        f.write(naive)
    try:
        info = leaninfo.run(tmp, parse_only=True, use_cache=False)
    finally:
        os.remove(tmp)

    def module(c):
        return next((k for k, (a, b) in enumerate(spans) if a <= c.start.byte < b), None)

    seen, drop = {}, []
    for c in info.commands:
        k = module(c)
        if k is None or not c.names:
            continue
        if 'solution' in c.names:
            sys.exit('refusing: `theorem solution` already in %s; strip it (the verifier takes the '
                     'FIRST one)' % mods[k])
        decl = leanedit.text(info, c.index).strip()
        for n in c.names:
            if n in seen and seen[n] != decl:
                # same name, different declaration (two provers' helpers named `ev`): keeping the
                # first would silently rebind the second module's uses to the wrong definition
                sys.exit('refusing: %s in %s differs from an earlier declaration of the same name '
                         '-- rename one, or give each module its own namespace' % (n, mods[k]))
        if all(n in seen for n in c.names):
            sys.stderr.write('dropping duplicate %s from %s\n' % (', '.join(c.names), mods[k]))
            drop.append(c.index)
            continue
        for n in c.names:
            seen[n] = decl

    regions, closers = [], []
    for k, (a, b) in enumerate(spans):
        regions.append(leanedit.remove_commands(info, drop, a, b).rstrip('\n'))
        # the scopes this module opened and left open: those in force at its wrapper `end`
        end = next(c for c in info.commands if c.start.byte >= b)
        closers.append([leanedit.closer(info, o) for o, _ in reversed(end.context)
                        if o is not None and module(info.commands[o]) == k])
    lvls, regions = _universes(regions)
    out = hdr + ('universe %s\n' % ' '.join(lvls) if lvls else '')
    starts = []
    for r, cl in zip(regions, closers):
        out += '\n'
        starts.append(len(out.encode()))
        out += 'section\n' + r.strip('\n') + '\n' + ''.join(x + '\n' for x in cl) + 'end\n'
    return out, starts


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    out_path, mods = sys.argv[1], sys.argv[2:]
    merged, _ = merge(mods, scratch=os.path.dirname(os.path.abspath(out_path)))
    open(out_path, 'w', encoding='utf-8').write(merged)
    print('lines:', merged.count('\n'))


if __name__ == '__main__':
    main()
