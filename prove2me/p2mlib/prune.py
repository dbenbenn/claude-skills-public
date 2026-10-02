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
    drop, gone = set(), []
    for c in info.commands:
        # a command that declares names (a declId: theorem, Mathlib's lemma, def, structure, …)
        # goes when none of them is reached; notation and syntax declare no declId and stay
        if (c.decl_kind or c.names) and c.index not in needed:
            drop.add(c.index)
            gone += [d.name for d in info.decls if d.command == c.index and not d.generated]
        elif c.short_kind in DIAGNOSTIC:
            drop.add(c.index)
    dropped_vars = set()
    for c in info.commands:
        if c.short_kind in ('variable', 'attribute') and c.index not in drop:
            t = info.slice(c.start.byte, c.end.byte)
            if any(names.mentions(t, g) for g in gone):
                drop.add(c.index)
                if c.short_kind == 'variable':
                    dropped_vars |= set(_binder_names(t))
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
                                'removed': sorted(gone), 'imports_removed': drop_imports}


def apply(info, drop, drop_imports):
    """The pruned source."""
    out = leanedit.remove_commands(info, drop)
    for m in drop_imports:
        out = re.sub(r'(?m)^import\s+%s\s*\n' % re.escape(m), '', out, count=1)
    return out
