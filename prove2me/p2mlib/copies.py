"""Which declarations of a Lean file state a published theorem: copies found by statement, by Lean.

rewire.py used to find a copy only by its name (the published short name, primes dropped). Moore's
`reduced_iff` states `MooreFoelner.isReducedDiagram_iff` through a local predicate (`¬ CommonCaret S
T` for the published `¬ ∃ i …`) under another name, and was rewired by hand (2026-10-02). Here the
file is elaborated with the candidate published theorems imported beside its own imports, and
LeanInfo reports, for each theorem of the file, the candidates with the same statement: equal after
renaming universes, unfolding the file's own Prop-valued definitions and erasing proofs; binder names
and brackets never matter. Not definitional equality, which would equate `2 + 2 = 4` with `4 = 2 + 2`.

Candidates are the published theorems whose definitions the file can see (every `Definitions.*`
module the candidate reaches is reachable from the file's imports; a Mathlib-only theorem always
qualifies), except one whose full name the file declares itself: importing it would clash.
"""
import functools
import os
import re

from . import leaninfo
from .leantext import strip
from .workspace import workspace, published_by_full

OURS = ('Definitions', 'Theorems', 'Solutions')


def imports_of(text):
    """The modules a Lean source imports. Lean allows `import` only in the header, so after
    removing comments every line starting `import` is one."""
    return re.findall(r'^import\s+(\S+)', strip(text), re.M)


def _module_file(ws, mod):
    return os.path.join(ws, *mod.split('.')) + '.lean'


@functools.lru_cache(maxsize=None)
def _direct(ws, mod):
    p = _module_file(ws, mod)
    return tuple(imports_of(open(p, encoding='utf-8').read())) if os.path.exists(p) else ()


def reachable_definitions(ws, mods):
    """The `Definitions.*` modules reachable from `mods` through the workspace's own modules."""
    seen, out, stack = set(), set(), list(mods)
    while stack:
        m = stack.pop()
        if m in seen or m.split('.')[0] not in OURS:
            continue
        seen.add(m)
        if m.startswith('Definitions.'):
            out.add(m)
        stack += _direct(ws, m)
    return out


def candidates(ws, text, declared=()):
    """Published theorem modules a file with source `text` could have copied, as a sorted list."""
    visible = reachable_definitions(ws, imports_of(text))
    declared = set(declared)
    return sorted(p.module for full, p in published_by_full(ws).items()
                  if full not in declared and reachable_definitions(ws, [p.module]) <= visible)


def find(path, ws=None):
    """(info, {local full name: [published full names]}) for the theorems of `path` that state a
    published theorem. `info` is LeanInfo's elaboration with the candidates imported."""
    ws = ws or workspace()
    text = open(path, encoding='utf-8').read()
    declared = {n for c in leaninfo.run(path, parse_only=True, ws=ws).commands for n in c.names}
    info = leaninfo.run(path, ws=ws, candidates=candidates(ws, text, declared))
    return info, {d.name: list(d.same_statement_as) for d in info.decls if d.same_statement_as}
