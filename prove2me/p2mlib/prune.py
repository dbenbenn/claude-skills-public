"""Delete what a solution never uses, by Lean's own dependencies (LeanInfo), not by name matching.

Roots: `solution`, plus every declaration whose command carries attributes or is an `instance`
(tactics and typeclass resolution can use these without the proof term naming them -- `simp`
lemmas do appear in proof terms, but a tactic extension registered by attribute would not), plus
the targets of `attribute [...] x` commands. Reachability follows `uses_local`, which LeanInfo
folds through auxiliary constants, so `match`, `where`, `decreasing_by` and structure projections
are seen exactly. A declaration command goes when nothing it declares is reached; with it go the
`variable` and `attribute` commands that mention it and every diagnostic command (`#print`,
`#check`, `#eval`, `#reduce`). An `import Theorems.X` goes when no kept declaration uses a
constant of that module (`uses_imported`): that import would be a false graph edge.
"""
import re

from . import leanedit, names

DIAGNOSTIC = {'check', 'eval', 'print', 'printAxioms', 'reduce', 'check_failure', 'synth', 'evalBang'}


_OPEN = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}


def _binder_groups(variable_cmd):
    """[(text, names, type)] for the top-level binder groups of a `variable` command, or None when
    it does not parse as `variable` followed by bracketed groups. `[Group G]` has no names."""
    m = re.match(r'variable\s+', variable_cmd)
    if not m:
        return None
    t, i, out = variable_cmd, m.end(), []
    while i < len(t):
        if t[i].isspace():
            i += 1
            continue
        if t[i] not in _OPEN:
            return None
        depth, j = [], i
        while j < len(t):
            ch = t[j]
            if ch in _OPEN:
                depth.append(_OPEN[ch])
            elif depth and ch == depth[-1]:
                depth.pop()
                if not depth:
                    break
            j += 1
        if depth:
            return None
        inner = t[i + 1:j]
        names_part, sep, typ = inner.partition(':')
        out.append((t[i:j + 1], names_part.split() if sep else [], typ if sep else inner))
        i = j + 1
    return out


def _binder_names(variable_cmd):
    """The names a `variable` command binds: `variable (hb : HB) {x y : S} [inst : C]` -> hb, x, y, inst."""
    out = []
    for group in re.findall(r'[(\[{⦃]([^:()\[\]{}⦃⦄]*):', variable_cmd):
        out += group.split()
    return out


def plan(info):
    """(drop: set of command indices, drop_imports: [module], report: dict)."""
    by_name = {d.name: d for d in info.decls}
    roots = set()
    for d in info.decls:
        c = info.commands[d.command] if d.command is not None else None
        # an anonymous instance's name is generated (instInhabitedP), so instances root everything
        # their command declares; attributes root only what the command itself names
        if d.name == 'solution' or (c is not None and (c.decl_kind == 'instance' or (c.attrs and not d.generated))):
            roots.add(d.name)
    for c in info.commands:
        if c.short_kind == 'attribute':
            body = info.slice(c.start.byte, c.end.byte).split(']', 1)[-1]
            for tok in body.split():
                for d in info.decls:
                    if tok in (d.name, d.short):
                        roots.add(d.name)
    if 'solution' not in by_name:
        raise SystemExit('no `solution` declaration -- refusing to prune')
    seen, stack = set(roots), list(roots)
    while stack:
        d = by_name.get(stack.pop())
        for u in (d.uses_local if d else []):
            if u not in seen:
                seen.add(u); stack.append(u)
    # a command is needed when any constant it produced is reached (P.mk reached keeps `structure P`)
    needed = {by_name[n].command for n in seen if n in by_name and by_name[n].command is not None}
    drop, gone, declared_gone = set(), [], []
    # the constants each command produced; Batteries' `alias foo := bar` has no declId, so its
    # command reports no names and its constant counts as generated, yet it declares `foo` -- kept
    # while `bar` was pruned, it broke the solution (dense-subgroups, 2026-10-03)
    owned = {}
    for d in info.decls:
        if d.command is not None:
            owned.setdefault(d.command, []).append(d)
    for c in info.commands:
        # a command that declares names (a declId: theorem, Mathlib's lemma, def, structure, …, or
        # an `alias`) goes when none of them is reached. Notation and syntax stay: the parser and
        # macro constants they generate are never "used" by a term
        if (c.decl_kind or c.names or c.short_kind == 'alias') and c.index not in needed:
            drop.add(c.index)
            own = owned.get(c.index, [])
            gone += [d.name for d in own if not d.generated] or [d.name for d in own]
            # what a `variable` binder can name: the command's own declarations, not the fields
            # and projections it generates (a binder `{Q : Type*}` is not the field `Data.Q`)
            declared_gone += list(c.names) or [d.name for d in own]
        elif c.short_kind in DIAGNOSTIC:
            drop.add(c.index)
    dropped_vars, replace = set(), {}
    for c in info.commands:
        if c.short_kind in ('variable', 'attribute') and c.index not in drop:
            t = info.slice(c.start.byte, c.end.byte)
            if c.short_kind == 'attribute':
                if any(names.mentions(t, g) for g in gone):
                    drop.add(c.index)
                continue
            groups = _binder_groups(t)
            if groups is None:          # unparsed: the whole command, as before
                if any(names.mentions(t, g) for g in declared_gone):
                    drop.add(c.index)
                    dropped_vars |= set(_binder_names(t))
                continue
            # a group goes when its type names a dropped declaration, or a binder of a group
            # that went (`(d : Data μ G) (hd : d.ok)`); the others stay, so `{X} {μ}` outlive `d`
            bad, changed = set(), True
            while changed:
                changed = False
                lost = {n for k in bad for n in groups[k][1]}
                for k, (_, ns, typ) in enumerate(groups):
                    if k not in bad and (any(names.mentions(typ, g) for g in declared_gone)
                                         or any(names.mentions(typ, n) for n in lost)):
                        bad.add(k)
                        changed = True
            if not bad:
                continue
            dropped_vars |= {n for k in bad for n in groups[k][1]}
            if len(bad) == len(groups):
                drop.add(c.index)
            else:
                replace[c.index] = 'variable ' + ' '.join(g[0] for k, g in enumerate(groups) if k not in bad)
    # an `include hb` / `omit hb` naming a dropped variable's binder goes too ("invalid 'include',
    # variable `hb` has not been declared", Lodha-Moore S3a 2026-10-02)
    for c in info.commands:
        if c.short_kind in ('include', 'omit') and c.index not in drop:
            t = info.slice(c.start.byte, c.end.byte)
            if any(names.mentions(t, v) for v in dropped_vars):
                drop.add(c.index)
    used_modules = {u['module'] for d in info.decls if d.command not in drop for u in d.uses_imported}
    header = info.slice(0, info.commands[0].start.byte) if info.commands else ''
    drop_imports = [m for m in re.findall(r'^import\s+(Theorems\.\S+)', header, re.M) if m not in used_modules]
    return drop, drop_imports, {'declarations': len([d for d in info.decls if not d.generated]),
                                'removed': sorted(gone), 'imports_removed': drop_imports,
                                'replace': replace}


def module_imports(module):
    """The modules a workspace module imports (a published statement: Mathlib and bundles), or []."""
    import os
    from .workspace import workspace
    path = os.path.join(workspace(), *module.split('.')) + '.lean'
    if not os.path.exists(path):
        return []
    return re.findall(r'^import\s+(\S+)', open(path, encoding='utf-8').read(), re.M)


def bundles_to_restore(header, drop_imports, imports_of=module_imports):
    """The `Definitions.*` modules the dropped theorem imports brought in that the header does not
    import itself: a dropped import must not take a bundle that kept code reaches only through it
    (dense-subgroups, 2026-10-03: `open CannonFloydParry` lost its namespace)."""
    have = set(re.findall(r'^import\s+(\S+)', header, re.M))
    out = []
    for m in drop_imports:
        for d in imports_of(m) or []:
            if d.startswith('Definitions.') and d not in have and d not in out:
                out.append(d)
    return out


def restore_bundles(text, bundles):
    """`text` with an `import` line for each bundle, after its last `import Definitions.*` line
    (or before its first import when it has none)."""
    if not bundles:
        return text
    lines = text.split('\n')
    defs = [i for i, l in enumerate(lines) if l.startswith('import Definitions.')]
    at = defs[-1] + 1 if defs else next((i for i, l in enumerate(lines) if l.startswith('import ')), 0)
    return '\n'.join(lines[:at] + ['import ' + b for b in bundles] + lines[at:])


def apply(info, drop, drop_imports, replace=None, imports_of=module_imports):
    """The pruned source; `replace` ({command index: text}) is plan's report['replace']."""
    header = info.slice(0, info.commands[0].start.byte) if info.commands else ''
    out = leanedit.remove_commands(info, drop, reps=replace)
    for m in drop_imports:
        out = re.sub(r'(?m)^import\s+%s\s*\n' % re.escape(m), '', out, count=1)
    return restore_bundles(out, bundles_to_restore(header, drop_imports, imports_of))
