"""Delete what a solution never uses, by Lean's own dependencies (LeanInfo), not by name matching.

Roots: `solution`, plus every declaration whose command carries attributes or is an `instance`
(tactics and typeclass resolution can use these without the proof term naming them -- `simp`
lemmas do appear in proof terms, but a tactic extension registered by attribute would not), plus
the targets of `attribute [...] x` commands. Reachability follows `uses_local`, which LeanInfo
folds through auxiliary constants, so `match`, `where`, `decreasing_by` and structure projections
are seen exactly. A declaration command goes when nothing it declares is reached; with it go the
`variable` and `attribute` commands that mention it and every diagnostic command (`#print`,
`#check`, `#eval`, `#reduce`). An `import Theorems.X` goes when no kept declaration uses a
constant of that module (`uses_imported`): that import would be a false graph edge. A `Definitions.*` import
goes the same way when, in addition, kept code never mentions one of the bundle's namespaces
(`unused_bundles`); it is not a graph edge, only dead weight in the published proof.
"""
import re

from . import leanedit, names
from .leantext import strip as leantext_strip

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


_IDENT = re.compile(r"(?<![\w'!?\u2080-\u209c.])[^\W\d][\w'!?\u2080-\u209c]*(?:\.[^\W\d][\w'!?\u2080-\u209c]*)*")


def _scope_candidates(tok, c):
    """The full names an identifier `tok` can denote in command `c`: `tok` qualified by each
    prefix of the namespace in force (innermost first, then the root), and by each `open`."""
    if tok.startswith('_root_.'):
        return [tok[len('_root_.'):]]
    ns = c.namespace.split('.') if c.namespace else []
    out = ['.'.join(ns[:k] + [tok]) for k in range(len(ns), -1, -1)]
    for o in c.opens or []:
        n = o.get('namespace') if isinstance(o, dict) else None
        if n:
            out.append(n + '.' + tok)
    return out


def _resolves_gone(text, c, gone, kept, bound=()):
    """Does `text`, read in the scope of command `c`, name a declaration that is going? An
    identifier counts when every local declaration it can denote there is in `gone`; one that
    can also denote a kept declaration, or none of ours (a binder, a Mathlib name), does not.
    `bound` names (the command's own binders) shadow everything."""
    for tok in _IDENT.findall(leantext_strip(text)):
        if tok.split('.')[0] in bound:
            continue
        hit = [x for x in _scope_candidates(tok, c) if x in gone or x in kept]
        if hit and all(x in gone for x in hit):
            return True
    return False


NOTATIONS = {'notation', 'notation3', 'mixfix'}


def _notation_roots(info, by_name, roots):
    """Notation commands are never pruned, and Lean prechecks a notation's identifiers when the
    command runs ("Unknown identifier `sideA` at quotation precheck", OAI Kaplansky 2026-10-07).
    So every declaration a notation names, read in its scope, joins `roots`, and so do the
    declarations named by the in-scope `variable` binders it uses (`local notation "SA" => sideA
    len m j firstA ...`), recursively through those binders' types. Returns {variable command
    index: binder names a notation needs}, binders the variable pass must keep."""
    keep = {}
    for c in info.commands:
        if c.short_kind not in NOTATIONS:
            continue
        t = info.slice(c.start.byte, c.end.byte)
        body = t.split('=>', 1)[1] if '=>' in t else t
        vcmds = [i for _, cmds in (c.context or []) for i in cmds
                 if info.commands[i].short_kind == 'variable']
        pending = [(body, c)]
        need = set()
        while pending:
            text, scope = pending.pop()
            for tok in _IDENT.findall(leantext_strip(text)):
                for x in _scope_candidates(tok, scope):
                    if x in by_name:
                        roots.add(x)
                head = tok.split('.')[0]
                if head in need:
                    continue
                for i in vcmds:
                    vc = info.commands[i]
                    for _, ns, typ in _binder_groups(info.slice(vc.start.byte, vc.end.byte)) or []:
                        if head in ns:
                            need.add(head)
                            keep.setdefault(i, set()).update(ns)
                            pending.append((typ, vc))
    return keep


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
    notation_vars = _notation_roots(info, by_name, roots)
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
    # a binder type names a going declaration when, resolved in the variable command's own scope
    # (its namespace and opens), its identifier can only mean declarations that go. Short-name
    # matching could not tell two `DirectionFrame`s in two namespaces apart (OAI Gottschalk
    # 2026-10-07), and skipping every shared short name kept `(firstA : CA m j → VA)` after its
    # `TwoSideFullStage.CA` went because a kept `CA` lived elsewhere ("Unknown identifier `CA`",
    # OAI Kaplansky 2026-10-07)
    gone_full = set(declared_gone)
    kept_full = {d.name for d in info.decls if d.command is not None and d.command not in drop}
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
                if _resolves_gone(t.split(None, 1)[-1], c, gone_full, kept_full,
                                  set(_binder_names(t))):
                    drop.add(c.index)
                    dropped_vars |= set(_binder_names(t))
                continue
            # a group goes when its type names a dropped declaration, or a binder of a group
            # that went (`(d : Data μ G) (hd : d.ok)`); the others stay, so `{X} {μ}` outlive `d`
            # a name the command binds shadows any global of that short name: `{Q : Type*} [Field Q]`
            # does not mention a pruned `Foo.Q` (OAI Gottschalk port, 2026-10-07: every group naming
            # `Q` was dropped, and with it `[Field Q]`)
            bound = {n for g in groups for n in g[1]}
            bad, changed = set(), True
            while changed:
                changed = False
                lost = {n for k in bad for n in groups[k][1]}
                for k, (_, ns, typ) in enumerate(groups):
                    if set(ns) & notation_vars.get(c.index, set()):
                        continue                # a kept notation names this binder
                    if k not in bad and (_resolves_gone(typ, c, gone_full, kept_full, bound)
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
    kept = '\n'.join(info.slice(c.start.byte, c.end.byte) for c in info.commands if c.index not in drop)
    drop_imports += unused_bundles(header, used_modules, kept)
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


def bundle_namespaces(module):
    """The namespaces a workspace bundle declares (`namespace A.B` gives `A.B` and `A`), or []."""
    import os
    from .workspace import workspace
    path = os.path.join(workspace(), *module.split('.')) + '.lean'
    if not os.path.exists(path):
        return []
    out = []
    for n in re.findall(r'^\s*namespace\s+(\S+)', open(path, encoding='utf-8').read(), re.M):
        for k in range(1, n.count('.') + 2):
            p = '.'.join(n.split('.')[:k])
            if p not in out:
                out.append(p)
    return out


def unused_bundles(header, used_modules, kept_text, namespaces_of=bundle_namespaces):
    """The `Definitions.*` imports of `header` that kept code does not use: no constant of the bundle
    is used, and none of its namespaces is mentioned (a bundle can be needed for an `open` alone, as
    CannonFloydParry was for dense-subgroups). Lusin-Novikov standalone (2026-10-03) kept an unused
    Monod bundle carried over from the merged development."""
    out = []
    for m in re.findall(r'^import\s+(Definitions\.\S+)', header, re.M):
        if m in used_modules:
            continue
        if any(re.search(r"(?<![\w.'])%s(?![\w'])" % re.escape(n), kept_text) for n in namespaces_of(m) or []):
            continue
        out.append(m)
    return out


def bundles_to_restore(header, drop_imports, imports_of=module_imports):
    """The `Definitions.*` modules the dropped theorem imports brought in that the header does not
    import itself: a dropped import must not take a bundle that kept code reaches only through it
    (dense-subgroups, 2026-10-03: `open CannonFloydParry` lost its namespace)."""
    have = set(re.findall(r'^import\s+(\S+)', header, re.M))
    out = []
    for m in drop_imports:
        if not m.startswith('Theorems.'):
            continue                    # a dropped bundle is unused; what it imports is not restored
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
