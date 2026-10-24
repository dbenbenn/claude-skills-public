"""Does a carved file use every graph edge it declares?

A carved piece's graph edges are its `import Theorems.*` lines, and a carved bundle's are those plus
its `import Definitions.*` lines naming other bundles of the same carve. The carver infers some of
them from source text, so it can emit an import the file never uses; the file still compiles, and
the false edge would go into the published dependency graph (PosteriorReplicas 2026-10-23: the
kernel piece imported `PosteriorRegression.fixed_quadratic_memory` because a field token
`E.fixed_quadratic_memory` was read as that theorem).

The check reads the file's compiled .olean, so it costs seconds, not a compile per import:

1. lean/EdgeUses.lean lists, per imported module of ours, the constants the file's declarations
   name in their types and values. For a piece it walks from `solution` (and the file's
   instances); for a bundle or statement every declaration is exported, so it walks from all of
   them. An import nothing uses is UNUSED. One that only declarations unreachable from `solution`
   use is DEAD: reported for pruning, not counted as a false edge (an attributed lemma that a
   tactic uses without naming it would look the same).
2. A use that leaves no constant behind (`dsimp only [h]` with an rfl lemma `h`, a notation, an
   `open`) is invisible to step 1, so every UNUSED import is confirmed by compiling the file
   without it -- all of them at once, then one by one if that fails. Modules the file uses only
   through a removed import are imported directly in that compile (`restore`): an import needed
   only to bring in a bundle is still a false edge, and the fix replaces it by the bundle. An
   import the file does not compile without is NEEDED, whatever step 1 said.

When the scan fails, the fallback is one compile per checked import, without it: compiles ->
false. That fallback also calls an import redundant with a transitive one false.

The functions here are pure (Lean runs in the callers' callbacks), so the logic is tested offline
(tests/test_edgecheck.py, whose `test_measure_finds_a_false_import_edge` runs the Lean side on
the CarveDev fixture with P2M_LEAN=1).
"""
import json
import os
import re
import subprocess


IMPORT_LINE = re.compile(r'^import\s+(\S+)[ \t]*$', re.M)


def imports(text):
    return IMPORT_LINE.findall(text)


def candidates(text, kind, carved_bundles=()):
    """The imports of a carved file that are graph edges to check: every `Theorems.*` import, and
    for a bundle also every `Definitions.Def_<b>` with b a bundle of this carve."""
    own = {'Definitions.Def_' + b for b in carved_bundles}
    return [m for m in imports(text)
            if m.startswith('Theorems.') or (kind == 'bundle' and m in own)]


def classify(uses, cands):
    """{module: 'used' | 'dead' | 'unused'} for the candidate imports, from EdgeUses' output."""
    live, alls = uses['live'], uses['all']
    return {m: 'used' if m in live else 'dead' if m in alls else 'unused' for m in cands}


def without(text, remove, add=()):
    """`text` without the `import M` lines of `remove`, with `import A` lines for `add` after the
    last import that stays."""
    lines = text.split('\n')
    kept = [l for l in lines if not (IMPORT_LINE.fullmatch(l) and IMPORT_LINE.fullmatch(l).group(1) in remove)]
    last = max((i for i, l in enumerate(kept) if IMPORT_LINE.fullmatch(l)), default=-1)
    have = set(imports(text))
    extra = ['import ' + a for a in add if a not in have]
    return '\n'.join(kept[:last + 1] + extra + kept[last + 1:])


def restore(removed, used, imports_of, have):
    """The modules to import directly once `removed` go: those the file uses (`used`) that it
    reached only through a removed import, transitively."""
    out, seen, stack = [], set(), list(removed)
    while stack:
        m = stack.pop()
        for x in imports_of(m) or []:
            if x in seen or x in have:
                continue
            seen.add(x)
            if x in used:
                out.append(x)
            stack.append(x)
    return sorted(out)


def check(text, cands, uses, compile_ok, imports_of):
    """The verdict on one file.

    uses:        EdgeUses' {'live': {module: [constants]}, 'all': {...}}, or None when the scan
                 failed (fallback: one compile per import)
    compile_ok:  text -> bool, compiles a variant of the file
    imports_of:  module -> [its imports] (to restore what a removed import brought in)

    Returns {'method', 'imports': {module: verdict}, 'false': [...], 'restore': {module: [...]},
    'compiles': n}; verdicts: used, false (unused, and the file compiles without it), dead (only
    code unreachable from `solution` uses it), needed (the file does not compile without it).
    """
    res = {'method': 'constants' if uses is not None else 'recompile', 'imports': {}, 'false': [],
           'restore': {}, 'compiles': 0}
    if not cands:
        res['method'] = 'none'
        return res
    have = set(imports(text))
    if uses is None:
        for m in cands:
            res['compiles'] += 1
            res['imports'][m] = 'false' if compile_ok(without(text, {m})) else 'needed'
        res['false'] = [m for m in cands if res['imports'][m] == 'false']
        return res
    res['imports'] = classify(uses, cands)
    live = set(uses['live'])
    unused = [m for m in cands if res['imports'][m] == 'unused']

    def attempt(ms):
        add = restore(ms, live, imports_of, have)
        res['compiles'] += 1
        return add if compile_ok(without(text, set(ms), add)) else None

    if unused and attempt(unused) is not None:
        for m in unused:
            res['imports'][m] = 'false'
            r = restore([m], live, imports_of, have)
            if r:
                res['restore'][m] = r
    else:
        for m in unused:
            add = attempt([m]) if len(unused) > 1 else None
            res['imports'][m] = 'false' if add is not None else 'needed'
            if add:
                res['restore'][m] = add
    res['false'] = [m for m in cands if res['imports'][m] == 'false']
    return res


TOOL = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean', 'EdgeUses.lean')


def scan(module, roots, env, cwd, timeout=1200):
    """EdgeUses on a compiled module (LEAN_PATH in `env` finds it), or None when it fails."""
    r = subprocess.run(['lean', '--run', TOOL, module] + list(roots), cwd=cwd, env=env,
                       capture_output=True, text=True, timeout=timeout)
    out = r.stdout.strip().split('\n')[-1] if r.stdout.strip() else ''
    try:
        data = json.loads(out)
    except ValueError:
        return None
    return data if r.returncode == 0 and 'live' in data else None
