#!/usr/bin/env python3
"""Assemble one Lean file from a Blueprint (definitions + `sorry` lemmas) and Part files proving them.

usage: assemble_blueprint.py BLUEPRINT.lean OUT.lean PART.lean [PART.lean ...] [--target NAME]
           [--published STUB=Theorems.MODULE[:NAME] ...] [--allow-sorry]

The parallel-prover pattern (F-amenability child, Lodha–Moore Lemma 5.6, 2026-10-02): a Blueprint
states every lemma with `sorry` and proves the main theorem from them; each prover writes
`Part<X>.lean` (`import <Blueprint module>`, `namespace <NS>.Part<X>`) restating some Blueprint
lemmas verbatim with proofs. A Part's *target* is a theorem `<NS>.Part<X>.foo` for a Blueprint
stub `<NS>.foo`. This script:

* concatenates the Blueprint and the Parts (each in its own section, under the union of their
  imports) and has Lean elaborate that once (LeanInfo): the Parts import only the Blueprint, so
  the concatenation compiles exactly when they do, and every dependency -- a helper on a
  Blueprint definition, a Part target on its helpers, a Blueprint lemma on a stub -- is Lean's own
  (`uses_local`), not a guess from the names a text mentions;
* replaces each proved stub by `alias foo := <NS>.Part<X>.foo`, which depends on its target;
* orders the declarations by those dependencies, keeping each Part's own order, preferring the
  Blueprint's order and putting a Part's helpers just before the stub of the target they serve;
* writes each run of declarations from one scope inside a section that re-creates that scope:
  its namespace, and the `open`, `variable`, `universe`, `include`, `omit` and `set_option`
  commands in force there (p2mlib.leanedit.scope_wrap). A Part's `section B2 ... variable {X}
  ... end B2` around several targets therefore reaches every target that needs it; splitting the
  Parts as text put those lines in the wrong chunks ("Invalid name after end", FAmenChild).

Other commands (module docs, `attribute`, notation) travel with the next declaration of their
file; `#print`, `#check`, `#eval` lines go (q188). A Part (or the Blueprint) that leaves a namespace
or section open at its end gets the missing `end`s, with a note (q182). A chunk whose scope `open`s a
namespace that another file declares goes after that namespace's first declaration; when no order
allows it, the namespace leaves that chunk's `open` if the chunk uses nothing in it, else this
refuses, naming both (q181). A Blueprint theorem whose proof was started and left with a `sorry` is a
stub too when a Part proves a theorem of the same type under its name (q187).

OUT is then elaborated: an error exits nonzero (the file is kept for inspection), and so does any
declaration still using `sorry` (a stub no Part proves), named, unless --allow-sorry.

A `Solutions.*` module the Blueprint or a Part imports (other than the Blueprint itself) is inlined
before the Blueprint, as merge.py inlines the modules it is given (each its own section,
duplicates dropped), with the `Solutions.*` modules it imports in turn, dependencies first: a
solution may import only Mathlib, `Definitions.*` and `Theorems.*`, and the assembled file kept
`import Solutions.TaoBRCS.Tools` (oaiq-121). A module with no file under the workspace is refused.
Its root-level commands (merge.py's hoisted `universe`) are in force throughout OUT, so no chunk
re-creates them (q167: "a universe level named u3 has already been declared").
A Part that another Part imports (`import Solutions.Viterbo.PP2PartL`, for its target) and that is
also given on the command line is not inlined: it is assembled once, as a Part, ahead of the Parts
that import it (inlined and assembled, it was "already declared", q155). A helper that imports the
Blueprint or a Part, directly or through another helper, uses their text: it is assembled as a Part
(after what it uses), not inlined ahead of the Blueprint (q188: "unknown identifier tOp").
A helper that is itself a Blueprint -- it has a `sorry`, and a Part on the command line imports it or
opens `namespace <its namespace>.Part<X>` -- is stacked, not inlined: it is assembled as a Blueprint
ahead of this one, its stubs replaced by the Parts that restate them, and those Parts are placed ahead
of their users (q284: Q284Cnt on Q284Sch, whose stubs were kept although Parts S1-S4 were given).

Parts come in two layouts, told apart per Part:
* import: the Part imports the Blueprint module (above);
* copy-header (Tao §4, q159): the Part imports only Mathlib, `Definitions.*` and `Theorems.*` and
  copies, at its head, the Blueprint definitions it needs and, as `sorry` stubs (`-- ASSUMED FROM
  BLUEPRINT`), the Blueprint lemmas it assumes; the Blueprint is never a module. Each declaration
  of a Blueprint name is checked against the Blueprint, comments and layout aside (a copy: the
  same text; an assumed stub: the same statement) and dropped, as are copied module docs and
  `#print`/`#check` lines; the Part's own declarations then use the Blueprint's, exactly as an
  importing Part does, and are assembled as above (the stubs a Part assumes order it after the
  Parts that prove them). A stub the Part proves under the Blueprint's own name, with the stub's
  statement, is renamed into the Part (`theorem <Part>.foo`) and becomes its target (q195). A copy
  that differs, such a proof stated differently, or a remaining `sorry` that is not a Blueprint stub
  is refused.
A Part with neither (only its own names) is assembled as it is.
A Part's namespace must be `<Blueprint namespace>.Part<X>`: one `<P>.Part<X>` with P no Blueprint
namespace proves no stub, so a theorem there named like a stub left unproved is refused, naming the
expected namespace (a warning under --allow-sorry), and any other such namespace is warned about
(q353: `LML.Dev.Part<X>` kept all seven stubs silently).

--target NAME (the published theorem, which the Blueprint states verbatim and proves from its
stubs): OUT is then a solution file. The Blueprint's NAME is renamed NAME_dev (a development must
not declare the target's name: references/verifier-failures.md) and a root-level `theorem solution`
with NAME's statement, `exact NAME_dev <explicit arguments>`, closes the file. Without it OUT is a
development for build_solution.py, which finds the target's proof as `NAME_dev` the same way.
When the Blueprint proves it under another name instead, one Blueprint theorem whose last component is
NAME's or NAME's plus `_dev` (`TaoBR.TaoDecay.X` for `TaoBR.X`, q165; `X_dev`, q208), that theorem keeps
its name and `solution` calls it. Either way run `prune_solution.py OUT --check` before submitting.

--published STUB=Theorems.MODULE[:NAME] (repeatable): the stub is proved by the published theorem instead
of a Part, `exact NAME <its explicit arguments>`, and MODULE is imported (NAME defaults to the module's
theorem). This cuts a slow Blueprint proof into pieces at stubs published as statements (q196, q200,
q209 each did it by hand): assemble each piece with --target and the stubs it does not prove published.
The published form may be the stub's with definitions unfolded (`exact` unfolds them), but a published
statement whose bundle redeclares the Blueprint's definitions clashes; then publish the Blueprint's
definitions as that bundle first. A Part's proof of a published stub stays in OUT unused, and
prune_solution.py drops it.
"""
import argparse
import heapq
import os
import re
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))  # p2mlib
from p2mlib import leanedit, leaninfo  # noqa: E402
from p2mlib.leantext import explicit_binders, header_end, strip  # noqa: E402

STRUCTURAL = {'namespace', 'section', 'noncomputableSection', 'end', 'eoi', 'open', 'variable',
              'universe', 'include', 'omit', 'set_option'}


def imports(text):
    return re.findall(r'^import\s+(\S+)', strip(text[:header_end(text)]), re.M)


def module_path(mod, ws):
    return os.path.join(ws, *mod.split('.')) + '.lean'


def solution_imports(texts, skip, ws):
    """[(module, path)] of the `Solutions.*` modules `texts` import, other than `skip` (the
    Blueprint's own names), closed under their own `Solutions.*` imports, dependencies first."""
    out, seen = [], set(skip)

    def visit(mod, via):
        if mod in seen:
            return
        seen.add(mod)
        path = module_path(mod, ws)
        if not os.path.exists(path):
            sys.exit('refusing: %s imports %s, which has no file %s to inline (a submission cannot '
                     'import Solutions.*)' % (via, mod, path))
        for m in imports(open(path, encoding='utf-8').read()):
            if m.startswith('Solutions.'):
                visit(m, mod)
        out.append((mod, path))
    for k, t in enumerate(texts):
        for m in imports(t):
            if m.startswith('Solutions.'):
                visit(m, 'the Blueprint' if k == 0 else 'a Part')
    return out


def header_imports(texts, skip):
    """The assembled file's imports: every import of `texts` but the Blueprint's (`skip`) and any
    other `Solutions.*` module (inlined), first-seen order."""
    hdr = []
    for t in texts:
        hdr += [m for m in imports(t) if m not in skip and not m.startswith('Solutions.') and m not in hdr]
    return hdr


def same_file(a, b):
    """The same file by path, or a copy of it with the same text."""
    if os.path.realpath(a) == os.path.realpath(b):
        return True
    try:
        return open(a, 'rb').read() == open(b, 'rb').read()
    except OSError:
        return False


def imported_parts(helpers, parts):
    """{module: index into `parts`} of the `Solutions.*` modules to inline that are Parts given on the
    command line: such a Part is assembled once, as a Part, not inlined too. q155 (Viterbo): Part G
    imported Part L for its target, and Part L, inlined through that import and assembled as a Part,
    was "already declared"."""
    out = {}
    for m, path in helpers:
        k = next((k for k, f in enumerate(parts) if same_file(path, f)), None)
        if k is not None:
            out[m] = k
    return out


def promote_helpers(helpers, bp_mods, imported):
    """The modules among `helpers` (dependencies first) that import the Blueprint or a Part, directly
    or through another such helper. They use Blueprint text, so they cannot be inlined ahead of it:
    each is assembled as a Part, placed by the dependency sort after what it uses (q188, S9 Pisier:
    `PartD_Defs` inlined ahead of the Blueprint, "unknown identifier tOp")."""
    out = []
    for m, path in helpers:
        if m not in imported and any(x in bp_mods or x in imported or x in out
                                     for x in imports(open(path, encoding='utf-8').read())):
            out.append(m)
    return out


def inner_blueprints(helpers, parts):
    """The modules among `helpers` (dependencies first) that are Blueprints themselves: a `sorry` in
    their text, and a Part on the command line that imports one directly or opens `namespace
    <one of its namespaces>.Part<X>`. They are assembled as Blueprints, not inlined: each in its own
    span ahead of the main Blueprint, its stubs replaced by the Parts that restate them, and those
    Parts placed ahead of their users by the dependency sort (q284: Q284Cnt imported the Blueprint
    Q284Sch; Sch was inlined with its stubs kept although its Parts S1-S4 were given, and the worker
    assembled Sch by hand first)."""
    ptexts = [open(f, encoding='utf-8').read() for f in parts]
    pimports = {m for t in ptexts for m in imports(t)}
    pns = {n for t in ptexts for n in re.findall(r'^\s*namespace\s+(\S+)\.Part[^.\s]*\s*$', strip(t), re.M)}
    out = []
    for m, path in helpers:
        if any(same_file(path, f) for f in parts):
            continue
        text = strip(open(path, encoding='utf-8').read())
        if not re.search(r'(?<![\w.])sorry(?!\w)', text):
            continue
        own = set(re.findall(r'^\s*namespace\s+(\S+)', text, re.M))
        if m in pimports or own & pns:
            out.append(m)
    return out


def order_parts(texts, imported):
    """Indices of the Parts (`texts`) in assembly order: each after the Parts it imports (`imported`,
    from imported_parts), otherwise as given."""
    need = [{imported[m] for m in imports(t) if m in imported} for t in texts]
    order = []
    while len(order) < len(texts):
        ready = [k for k in range(len(texts)) if k not in order and need[k] <= set(order)]
        if not ready:
            sys.exit('refusing: Parts import each other in a cycle: %s'
                     % ', '.join(m for m, k in imported.items() if k not in order))
        order.append(ready[0])
    return order


def _norm(s):
    return ' '.join(s.split())


def _code(info, i, start=None, end=None):
    """Command i's code from `start` to `end` (bytes; default its own range), comments and layout
    aside: how a copy is compared with its Blueprint original."""
    c = info.commands[i]
    return _norm(strip(info.slice(c.start.byte if start is None else start, c.end.byte if end is None else end)))


def _is_sorry(info, i):
    c = info.commands[i]
    return bool(c.value_start) and bool(re.fullmatch(r':=\s*(by\s+)?sorry', _code(info, i, c.value_start.byte)))


def _has_sorry(info, i):
    """Command i's value (its proof) mentions `sorry` anywhere, comments aside: a stub, or a proof
    started and left unfinished (q187)."""
    c = info.commands[i]
    return bool(c.value_start) and re.search(r'(?<![\w.])sorry(?![\w])', _code(info, i, c.value_start.byte)) is not None


def _statement(info, i):
    c = info.commands[i]
    return _code(info, i, end=c.value_start.byte) if c.value_start else _code(info, i)


def drop_copies(info, bp, label):
    """(text, copied, assumed) for a Part (`info`, its parse) checked against the Blueprint (`bp`): the
    Part's text without the declarations of Blueprint names it copies, `copied` those names and
    `assumed` the stubs it restates with `sorry`. A copy must be the Blueprint's text and an assumed
    stub its statement, comments and layout aside, else this refuses. A Part with no such copy is an
    ordinary Part: its text comes back unchanged. In a copy-header Part, copied module docs and
    `#print`-style commands go too, and any other `sorry` is refused (q159: the one-off
    assemble.py scripts of tao-br-mission/proofs/{thm410,parab,pbr} did the same by text)."""
    bp_decl = {n: c.index for c in bp.commands for n in c.names}
    bp_anon = {_code(bp, c.index) for c in bp.commands if c.short_kind == 'declaration' and not c.names}
    bp_docs = {_norm(leanedit.text(bp, c.index)) for c in bp.commands if c.short_kind == 'moduleDoc'}
    drop, copied, assumed, extra, own_sorry, moved, reps = [], [], [], [], [], [], {}
    for c in info.commands:
        i = c.index
        hit = [n for n in c.names if n in bp_decl]
        if hit:
            j = bp_decl[hit[0]]
            if len(hit) != len(c.names) or any(bp_decl[n] != j for n in hit):
                sys.exit('refusing: %s declares %s together, which the Blueprint does not'
                         % (label, ', '.join(c.names)))
            if _is_sorry(info, i):
                if _statement(info, i) != _statement(bp, j):
                    sys.exit('refusing: %s assumes %s, stated differently from the Blueprint:\n  %s:  %s\n'
                             '  Blueprint: %s' % (label, hit[0], label, _statement(info, i), _statement(bp, j)))
                assumed += hit
            elif _has_sorry(bp, j):
                # q195: the Part proves a stub under the Blueprint's own name. With the stub's statement
                # it is the Part's target, moved into its namespace (`theorem <label>.foo`), where the
                # stub's alias finds it; the Part's own uses of `foo` then reach it through that alias
                if _statement(info, i) != _statement(bp, j):
                    sys.exit('refusing: %s proves the Blueprint stub %s under the Blueprint\'s own name, stated '
                             'differently:\n  %s:  %s\n  Blueprint: %s\nrestate it verbatim, or prove it as '
                             '<NS>.%s.%s' % (label, hit[0], label, _statement(info, i), _statement(bp, j),
                                            label, hit[0].rsplit('.', 1)[-1]))
                a = c.ids[0][0].byte
                reps[i] = info.slice(c.start.byte, a) + label + '.' + info.slice(a, c.end.byte)
                moved += hit
                continue
            elif _code(info, i) != _code(bp, j):
                sys.exit('refusing: %s copies %s, but not verbatim from the Blueprint:\n  %s:  %s\n  Blueprint: %s'
                         % (label, hit[0], label, _code(info, i), _code(bp, j)))
            else:
                copied += hit
            drop.append(i)
        elif c.short_kind == 'declaration' and not c.names and _code(info, i) in bp_anon:
            drop.append(i)                         # an anonymous instance, copied
        elif c.short_kind == 'moduleDoc' and _norm(leanedit.text(info, i)) in bp_docs:
            extra.append(i)
        elif leanedit.text(info, i).startswith('#'):
            extra.append(i)                        # #print axioms ..., #check
        elif c.short_kind == 'declaration' and _is_sorry(info, i):
            own_sorry += c.names or [str(c.start.line)]
    if not drop and not reps:
        return info.text_bytes.decode('utf-8'), [], []
    if own_sorry:
        sys.exit('refusing: %s still has `sorry` in %s, which the Blueprint does not state: an assumption '
                 'the assembly cannot discharge' % (label, ', '.join(own_sorry)))
    if moved:
        print('%s: proves %s under the Blueprint\'s own name; assembled as %s' % (
            label, ', '.join(moved), ', '.join('%s.%s.%s' % (m.rsplit('.', 1)[0], label, m.rsplit('.', 1)[1])
                                               if '.' in m else '%s.%s' % (label, m) for m in moved)))
    return leanedit.remove_commands(info, drop + extra, reps=reps), copied, assumed


def parse_part(path, scratch):
    """The parse-only LeanInfo of a Part or Blueprint file, its `import Solutions.*` lines blanked
    (spaces, so every offset stays): those modules need not be built, only inlined later."""
    raw = open(path, 'rb').read()
    text = raw.decode('utf-8')
    k = len(text[:header_end(text)].encode('utf-8'))
    head = re.sub(rb'(?m)^import\s+Solutions\.\S+', lambda m: b' ' * len(m.group(0)), raw[:k])
    fd, tmp = tempfile.mkstemp(suffix='.lean', prefix='.assemble_parse_', dir=scratch)
    with os.fdopen(fd, 'wb') as f:
        f.write(head + raw[k:])
    try:
        info = leaninfo.run(tmp, parse_only=True, use_cache=False)
    finally:
        os.remove(tmp)
    info.text_bytes = raw
    return info


def published_name(module, ws):
    """The full name of the theorem a published Theorems module states: its first `theorem`, under the
    module's `namespace` when it opens one and the name is not already qualified by it."""
    path = module_path(module, ws)
    try:
        text = strip(open(path, encoding='utf-8').read())
    except OSError:
        sys.exit('refusing: --published: no file %s for %s (fetch_theorems.py --names first)' % (path, module))
    m = re.search(r'^\s*(?:theorem|lemma)\s+([^\s:({\[]+)', text, re.M)
    if not m:
        sys.exit('refusing: --published: %s states no theorem; give its name as MODULE:NAME' % module)
    name = m.group(1)
    ns = re.search(r'^namespace\s+(\S+)', text[:m.start()], re.M)
    if ns and not name.startswith(ns.group(1) + '.'):
        name = ns.group(1) + '.' + name
    return name


def renamed(info, i, suffix='_dev'):
    """Command i's text with its declared name renamed `<name><suffix>`."""
    c = info.commands[i]
    b = c.ids[0][1].byte
    return info.slice(c.start.byte, b) + suffix + info.slice(b, c.end.byte)


def solution_text(info, i, target, suffix='_dev', replace=None):
    """A root-level `theorem solution` with the statement of command i (the Blueprint's `target`),
    proved by `exact <target><suffix> <its explicit arguments>`, in a section re-creating i's scope
    (`replace`: as for leanedit.scope_wrap)."""
    c = info.commands[i]
    sig = info.slice(c.ids[0][1].byte, c.value_start.byte).rstrip()
    pre, post = leanedit.scope_wrap(info, i, top_level=True, replace=replace)
    return pre + 'theorem solution%s := by\n  exact %s%s%s\n' % (
        sig, target, suffix, ''.join(' ' + x for x in explicit_binders(sig))) + post


def blueprint_modules(bpf, part_texts, ws):
    """The module names under which the Parts import the Blueprint: its own module, from its path
    under the workspace (CFW's blueprint is Solutions/CFW/Route.lean), and, as before, any
    imported module named *Blueprint."""
    rel = os.path.relpath(os.path.abspath(bpf), os.path.abspath(ws))
    own = set() if rel.startswith('..') else {os.path.splitext(rel)[0].replace(os.sep, '.')}
    named = {m for t in part_texts for m in imports(t) if m.endswith('Blueprint')}
    if own:
        # its own module known, another *Blueprint is one only as a copy of it: else it is a Blueprint
        # this one stacks on (q284), inlined or assembled, never dropped
        named = {m for m in named if not os.path.exists(module_path(m, ws)) or same_file(module_path(m, ws), bpf)}
    return own | named


def label(path):
    return os.path.splitext(os.path.basename(path))[0]


DIAGNOSTIC = re.compile(r'#(print|check|eval|reduce|synth)\b')
SORRY_WARNING = re.compile(r"declaration uses .sorry.")


def concat_of(header, texts, closers):
    """The Blueprint and the Parts after `header`, each in its own section, with the `end`s of the
    scopes it leaves open (`closers`) before that section's `end`; and each file's byte span in it."""
    concat, spans = header, []
    for t, cl in zip(texts, closers):
        concat += 'section\n'
        a = len(concat.encode())
        concat += t[header_end(t):].rstrip('\n') + '\n'
        spans.append((a, len(concat.encode())))
        concat += ''.join(x + '\n' for x in cl) + 'end\n'
    return concat, spans


def elaborate(text, scratch):
    fd, tmp = tempfile.mkstemp(suffix='.lean', prefix='.assemble_', dir=scratch)
    with os.fdopen(fd, 'w', encoding='utf-8') as f:
        f.write(text)
    try:
        return leaninfo.run(tmp, use_cache=False)
    finally:
        os.remove(tmp)


def left_open(info, spans):
    """For each file's span, the `end`s (innermost first) of the namespaces and sections it opened
    and left open: legal at the end of a file, but concatenated, the wrapper's `end` met them
    ("Missing name after `end`: Expected the current scope name", q182)."""
    out = []
    for a, b in spans:
        stop = next(c for c in info.commands if c.start.byte >= b)
        out.append([leanedit.closer(info, o) for o, _ in reversed(stop.context)
                    if o is not None and a <= info.commands[o].start.byte < b])
    return out


def registers(c):
    """The namespaces that exist once command c is in place: its own and its names' prefixes."""
    out = set()
    for n in [c.namespace] + [n.rsplit('.', 1)[0] for n in c.names if '.' in n]:
        parts = n.split('.') if n else []
        out |= {'.'.join(parts[:k]) for k in range(1, len(parts) + 1)}
    return out


def opened(info, o):
    """The namespaces the `open` command o opens, as Lean resolved them."""
    before = {x.get('namespace') for x in info.commands[o].opens}
    nxt = info.commands[o + 1].opens if o + 1 < len(info.commands) else []
    return [x['namespace'] for x in nxt if x.get('namespace') and x['namespace'] not in before]


def drop_namespaces(open_text, gone):
    """`open_text` (an `open` command) without the namespaces `gone`, or None when nothing is left.
    ValueError for an `open` of another shape (`hiding`, `renaming`, `(…)`, `in`)."""
    m = re.fullmatch(r'open\s+((?:scoped\s+)?)(.+?)\s*', strip(open_text), re.S)
    toks = m.group(2).split() if m else []
    if not m or any(not re.fullmatch(r'[^\s()]+', t) or t in ('hiding', 'renaming', 'in') for t in toks):
        raise ValueError(open_text)
    keep = [t for t in toks if not any(g == t or g.endswith('.' + t) for g in gone)]
    return 'open %s%s' % (m.group(1), ' '.join(keep)) if keep else None


def imported_namespaces(imports_text, names, scratch):
    """The namespaces among `names` that the imports alone declare (Lean opens them without error)."""
    probe = imports_text + ''.join('section\nopen %s\nend\n' % n for n in names)
    bad = {m.start.line for m in elaborate(probe, scratch).errors}
    first = imports_text.count('\n') + 2
    return {n for j, n in enumerate(names) if first + 3 * j not in bad}


def toposort(items, deps, pref):
    """`items` ordered so each comes after its `deps`, by `pref` where free; on a cycle, only those
    placed before it."""
    users = {i: [] for i in items}
    indeg = {i: len(deps[i]) for i in items}
    for i in items:
        for j in deps[i]:
            users[j].append(i)
    heap = [pref[i] for i in items if indeg[i] == 0]
    heapq.heapify(heap)
    order = []
    while heap:
        _, i = heapq.heappop(heap)
        order.append(i)
        for u in users[i]:
            indeg[u] -= 1
            if indeg[u] == 0:
                heapq.heappush(heap, pref[u])
    return order


def stub_candidates(c, n, label):
    """The Blueprint stubs a Part's theorem `n` (command c, from the Part `label`) may prove: `n` with
    the last component of its namespace taken out (`<NS>.Part<X>.foo` proves `<NS>.foo`), and with
    the component `label` taken out (`theorem <label>.foo` in `<NS>`, as drop_copies renames a
    stub proved under the Blueprint's own name, q195)."""
    out = []
    if c.namespace and n.startswith(c.namespace + '.'):
        out.append(c.namespace.rsplit('.', 1)[0] + n[len(c.namespace):])
    if label and '.' + label + '.' in '.' + n:
        out.append(('.' + n).replace('.' + label + '.', '.', 1)[1:])
    return out


def misplaced_parts(part_ns, bp_ns, unproved):
    """(refusals, warnings) for the Parts whose namespace is `<P>.Part<X>` (the last component starting
    `Part`) with P no namespace of a Blueprint (`bp_ns`): their theorems match no stub, so the assembly
    kept every stub it meant to prove (q353: `LML.Dev.Part<X>` for `LML.Part<X>`). `part_ns` maps (Part
    label, namespace) to the names declared there; a refusal when one of them has the last component of
    a stub no Part proves (`unproved`), naming `<stub namespace>.Part<X>`, else a warning naming the
    expected namespaces."""
    refuse, warn = [], []
    for (lab, ns), names in sorted(part_ns.items()):
        comps = ns.split('.')
        k = max((j for j, x in enumerate(comps) if x.startswith('Part')), default=None)
        if k is None or '.'.join(comps[:k]) in bp_ns:
            continue
        part = '.'.join(comps[k:])
        lasts = {n.rsplit('.', 1)[-1] for n in names}
        hits = sorted(s for s in unproved if s.rsplit('.', 1)[-1] in lasts)
        if hits:
            want = sorted({'%s.%s' % (s.rsplit('.', 1)[0], part) if '.' in s else part for s in hits})
            refuse.append('%s restates %s in namespace %s, which proves no stub: a Part\'s namespace is '
                          '<Blueprint namespace>.Part<X>, expected %s' % (lab, ', '.join(hits), ns, ' or '.join(want)))
        else:
            want = sorted('%s.%s' % (b, part) if b else part for b in bp_ns)
            warn.append('%s: namespace %s is not <Blueprint namespace>.Part<X> (expected %s); its theorems prove '
                        'no Blueprint stub' % (lab, ns, ' or '.join(want)))
    return refuse, warn


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('blueprint')
    ap.add_argument('out')
    ap.add_argument('parts', nargs='+')
    ap.add_argument('--target', help='the published theorem: rename it NAME_dev and append `theorem solution`')
    ap.add_argument('--published', action='append', default=[], metavar='STUB=MODULE[:NAME]',
                    help='prove Blueprint stub STUB by the published theorem of Theorems module MODULE (its '
                         'theorem NAME, read from the module when omitted) and import MODULE')
    ap.add_argument('--allow-sorry', action='store_true',
                    help='exit 0 although declarations of OUT still use `sorry` (stubs no Part proves)')
    args = ap.parse_args()
    bpf, out, parts = args.blueprint, args.out, list(args.parts)
    from p2mlib.workspace import workspace
    ws = workspace()

    def read(f):
        return open(f, encoding='utf-8').read()
    ptexts = [read(f) for f in parts]
    bp_mods = blueprint_modules(bpf, ptexts, ws)
    helpers = solution_imports([read(bpf)] + ptexts, bp_mods, ws)
    inner = inner_blueprints(helpers, parts)
    inner_paths = [p for m, p in helpers if m in inner]
    for p in inner_paths:
        print('%s: a Blueprint with `sorry` stubs that a Part on the command line restates; assembled as a '
              'Blueprint ahead of this one, its stubs replaced (not inlined)' % label(p))
    bp_mods |= set(inner)
    helpers = [h for h in helpers if h[0] not in inner]
    imported = imported_parts(helpers, parts)
    promoted = promote_helpers(helpers, bp_mods, imported)
    for m, path in helpers:
        if m in promoted:
            print('%s: imports the Blueprint or a Part; assembled as a Part, after what it uses (not inlined)'
                  % label(path))
            parts.append(path)
    imported = imported_parts(helpers, parts)
    ptexts = [read(f) for f in parts]
    for m, k in imported.items():
        if m not in promoted:
            print('%s: imported by %s; assembled once, as a Part, ahead of it (not inlined)' % (
                label(parts[k]), ', '.join(label(p) for p, t in zip(parts, ptexts) if m in imports(t))))
    helpers = [h for h in helpers if h[0] not in imported]
    parts = [parts[k] for k in order_parts(ptexts, imported)]
    # the Blueprints, inner ones first (they come before what imports them), then the Parts
    files = inner_paths + [bpf] + parts
    nbp = len(inner_paths) + 1
    main_bp = nbp - 1
    texts = [read(f) for f in files]
    owners = [label(p) for p in inner_paths] + [None] + [label(p) for p in parts]
    # copy-header Parts (q159): their copies of Blueprint text, checked, are dropped; a Part importing
    # the Blueprint is not parsed at all
    scratch = os.path.dirname(os.path.abspath(out))
    bp_info = None
    for k in range(nbp, len(files)):
        if not set(imports(texts[k])) & bp_mods:
            bp_info = bp_info or parse_part(bpf, scratch)
            texts[k], copied, assumed = drop_copies(parse_part(files[k], scratch), bp_info, owners[k])
            if copied or assumed:
                print('%s: dropped its copy of %s; assumes %s' % (
                    owners[k], ', '.join(copied) or 'nothing', ', '.join(assumed) or 'nothing'))
    pre = ''
    if helpers:
        # inlined as merge.py would, ahead of the Blueprint and outside every Part's span, so they
        # are never reordered, aliased or taken for stubs (oaiq-121)
        from merge import merge
        merged, _ = merge([p for _, p in helpers], scratch=scratch)
        pre = merged[header_end(merged):].rstrip('\n') + '\n'
        print('inlined %s' % ', '.join(m for m, _ in helpers))
    hdr = header_imports([read(p) for _, p in helpers] + texts, bp_mods)
    published = {}                                 # stub as given -> (module, theorem name)
    for spec in args.published:
        stub, _, mod = spec.partition('=')
        mod, _, name = mod.partition(':')
        if not stub or not mod.startswith('Theorems.'):
            sys.exit('refusing: --published %s: write STUB=Theorems.MODULE[:NAME]' % spec)
        published[stub] = (mod, name or published_name(mod, ws))
        if mod not in hdr:
            hdr.append(mod)
    imports_text = ''.join('import %s\n' % m for m in hdr)
    header = imports_text + pre
    closers = [[] for _ in texts]
    while True:
        concat, spans = concat_of(header, texts, closers)
        info = elaborate(concat, scratch)
        found = left_open(info, spans)
        new = [k for k, cl in enumerate(found) if cl and not closers[k]]
        if not new:
            break
        for k in new:
            closers[k] = found[k]
            sys.stderr.write('%s leaves %s open at its end: closed with `%s`\n' % (
                owners[k] or 'the Blueprint', 'a scope' if len(closers[k]) == 1 else 'scopes',
                '`, `'.join(closers[k])))
    if info.errors:
        sys.exit('the Blueprint with its Parts does not elaborate:\n' + '\n'.join(
            'line %d: %s' % (m.start.line, m.text[:300]) for m in info.errors[:8]))

    def owner_of(c):
        return next((k for k, (a, b) in enumerate(spans) if a <= c.start.byte < b), None)

    cmds = info.commands
    # the inlined helpers' root-level commands (merge.py's hoisted `universe`) are in force at the root
    # of OUT: re-created in every chunk they were declared twice (q167). Their diagnostics go.
    pre_lo, pre_hi = len(imports_text.encode()), spans[0][0] - len('section\n')
    in_pre = [c.index for c in cmds if pre_lo <= c.start.byte < pre_hi]
    diag = [i for i in in_pre if DIAGNOSTIC.match(leanedit.text(info, i))]
    if diag:
        header = imports_text + leanedit.remove_commands(info, diag, pre_lo, pre_hi)
    at_root = {i: None for i in in_pre}
    pre_reg = set().union(*[registers(cmds[i]) for i in in_pre]) if in_pre else set()

    declares = {d.command for d in info.decls if d.command is not None}
    items = [c.index for c in cmds if owner_of(c) is not None and c.short_kind not in STRUCTURAL
             and (c.index in declares or c.names or c.decl_kind)]
    item_set = set(items)
    # other commands go with the next declaration of their file (else the previous one); `#print`,
    # `#check`, `#eval` go (q188: a stray `#print axioms` split PartB)
    attached = {i: [] for i in items}
    for c in cmds:
        k = owner_of(c)
        if k is None or c.index in item_set or c.short_kind in STRUCTURAL \
                or DIAGNOSTIC.match(leanedit.text(info, c.index)):
            continue
        nxt = [i for i in items if owner_of(cmds[i]) == k and i > c.index]
        prv = [i for i in items if owner_of(cmds[i]) == k and i < c.index]
        if nxt or prv:
            attached[nxt[0] if nxt else prv[-1]].append(c.index)

    def value(i):
        c = cmds[i]
        return info.slice(c.value_start.byte, c.end.byte) if c.value_start else ''

    decl_of = {d.name: d for d in info.decls}
    def in_bp(c):
        k = owner_of(c)
        return k is not None and k < nbp

    stubs = {n: c.index for c in cmds if in_bp(c) and c.decl_kind == 'theorem'
             for n in c.names if re.fullmatch(r':=\s*(by\s+)?sorry\s*', value(c.index))}
    # a Blueprint proof started and left with a `sorry` (q187): a stub when a Part restates it
    partial = {n: c.index for c in cmds if in_bp(c) and c.decl_kind == 'theorem'
               for n in c.names if n not in stubs and re.search(r'(?<![\w.])sorry(?!\w)', strip(value(c.index)))}
    proved = {}                                    # stub full name -> target command
    for i in items:
        c = cmds[i]
        k = owner_of(c)
        if k >= nbp and c.decl_kind == 'theorem':
            for n in c.names:
                for stub in stub_candidates(c, n, owners[k]):
                    if stub in partial and stub in decl_of and n in decl_of \
                            and decl_of[stub].type_hash == decl_of[n].type_hash:
                        stubs[stub] = partial.pop(stub)
                        print('%s: proves %s, which the Blueprint left unfinished; replaced as a stub'
                              % (owners[k], stub))
                    # q200: a Part's helper may share a stub's name with another statement (PartG's
                    # `card_dyadic_le`, `0 < M`, beside the stub's `0 ≤ M`); only a theorem of the
                    # stub's type proves it, and a proof already found is kept
                    if stub in stubs and stub not in proved and (
                            stub not in decl_of or n not in decl_of
                            or decl_of[stub].type_hash == decl_of[n].type_hash):
                        proved[stub] = i
    pub_of = {}                                    # stub command -> published theorem name
    for given, (mod, name) in published.items():
        hits = [n for n in set(stubs) | set(partial) if n == given or n.rsplit('.', 1)[-1] == given]
        if len(hits) != 1:
            sys.exit('refusing: --published %s: %s' % (given, 'not a Blueprint stub (a theorem proved by `sorry`)'
                     if not hits else 'several stubs match: %s; give the full name' % ', '.join(sorted(hits))))
        n = hits[0]
        if n in partial:
            stubs[n] = partial.pop(n)
        proved.pop(n, None)                        # a Part's proof of it is no longer used (prune drops it)
        pub_of[stubs[n]] = name
        print('%s: proved by the published %s (%s)' % (n, name, mod))
    alias_of = {stubs[s]: (s, t) for s, t in proved.items()}
    # q353: a Part namespaced outside the Blueprint's (`LML.Dev.Part<X>`) proved nothing, silently
    bp_ns = set()
    for i in items:
        if in_bp(cmds[i]):
            bp_ns.add(cmds[i].namespace or '')
            bp_ns |= {n.rsplit('.', 1)[0] if '.' in n else '' for n in cmds[i].names}
    part_ns = {}
    for i in items:
        k = owner_of(cmds[i])
        if k >= nbp and cmds[i].namespace:
            part_ns.setdefault((owners[k], cmds[i].namespace), []).extend(cmds[i].names)
    unproved = [n for n in set(stubs) | set(partial) if n not in proved and stubs.get(n) not in pub_of]
    refuse, warn = misplaced_parts(part_ns, bp_ns, unproved)
    for w in warn + (refuse if args.allow_sorry else []):
        sys.stderr.write('WARNING: %s\n' % w)
    if refuse and not args.allow_sorry:
        sys.exit('refusing: ' + '\nrefusing: '.join(refuse))

    cmd_of = {d.name: d.command for d in info.decls}
    deps = {i: set() for i in items}
    uses = {i: set() for i in items}
    for d in info.decls:
        if d.command in deps:
            uses[d.command] |= set(d.uses_local)
            if d.command not in alias_of:
                deps[d.command] |= {cmd_of[u] for u in d.uses_local if cmd_of.get(u) in deps} - {d.command}
    for i, (s, t) in alias_of.items():
        deps[i] = {t}
    tgt, suffix = None, '_dev'
    if args.target:
        named = [i for i in items if owner_of(cmds[i]) == main_bp and cmds[i].names]
        tgt = next((i for i in named if args.target in cmds[i].names), None)
        if tgt is None:
            # q165 (Tao decay leaf): proved in a Blueprint sub-namespace (TaoBR.TaoDecay.X for TaoBR.X);
            # a different name, so it keeps it and `solution` calls it
            last = args.target.rsplit('.', 1)[-1]
            cands = [i for i in named if cmds[i].decl_kind == 'theorem'
                     and any(n.rsplit('.', 1)[-1] in (last, last + '_dev') for n in cmds[i].names)]
            if len(cands) > 1:
                sys.exit('refusing: --target %s: the Blueprint has several theorems named %s: %s' % (
                    args.target, last, ', '.join(cmds[i].names[0] for i in cands)))
            if cands:
                tgt, suffix = cands[0], ''
                print('--target %s: the Blueprint proves it as %s' % (args.target, cmds[tgt].names[0]))
        if tgt is None or not cmds[tgt].value_start or not cmds[tgt].ids:
            sys.exit('refusing: the Blueprint does not prove %s (--target) under that name or its last '
                     'component; state and prove the published theorem there, or leave --target out and '
                     'wrap OUT with build_solution.py' % args.target)
        users = sorted({n for i in items if tgt in deps[i] for n in cmds[i].names})
        if suffix and users:
            sys.exit('refusing: %s use(s) %s by name; renamed %s_dev it would break them'
                     % (', '.join(users), args.target, args.target))
        if any('solution' in c.names for c in cmds):
            sys.exit('refusing: the input already declares a `solution`')
    for k in range(nbp, len(files)):               # a Part keeps its own order
        mine = [i for i in items if owner_of(cmds[i]) == k]
        for x, y in zip(mine, mine[1:]):
            deps[y].add(x)
    # preference: the Blueprint's order; a Part item just before the stub of its Part's next target
    bitems = [i for i in items if in_bp(cmds[i])]
    bpos = {i: n for n, i in enumerate(bitems)}
    target_stub = {t: stubs[s] for s, t in proved.items()}
    pref = {}
    for i in items:
        if in_bp(cmds[i]):
            pref[i] = (2 * bpos[i] + 1, i)
        else:
            later = [j for j in items if j >= i and owner_of(cmds[j]) == owner_of(cmds[i]) and j in target_stub]
            pref[i] = (2 * bpos[target_stub[later[0]]] if later else 2 * len(bitems), i)
    # a chunk whose scope `open`s a namespace this text declares goes after its first declaration
    # there (q181: PartT's `open Finset …PartG` was placed ahead of PartG: "unknown namespace")
    first_reg = {}
    for i in items:
        for ns in registers(cmds[i]):
            first_reg.setdefault(ns, i)
    ctx_opens = {}
    for i in items:
        ctx_opens[i] = [(o, loc) for _, cs in cmds[i].context for o in cs if cmds[o].short_kind == 'open'
                        for loc in [[ns for ns in opened(info, o)
                                     if ns not in pre_reg and first_reg.get(ns, o) < o]] if loc]
    with_opens = {i: deps[i] | {first_reg[ns] for _, loc in ctx_opens[i] for ns in loc} for i in items}
    order = toposort(items, with_opens, pref)
    if len(order) < len(items):
        order = toposort(items, deps, pref)
        if len(order) == len(items):
            sys.stderr.write('no order puts every chunk after the namespaces its `open` names; '
                             'those it does not use leave its `open`\n')
    if len(order) < len(items):
        stuck = [', '.join(cmds[i].names) or str(i) for i in items if i not in set(order)]
        sys.exit('dependency cycle among: %s (a Part helper using the stub its own Part proves?)'
                 % '; '.join(stuck[:12]))

    def text_of(i):
        if i in pub_of:
            c = cmds[i]
            sig = info.slice(c.ids[0][1].byte, c.value_start.byte).rstrip()
            return '%s := by\n  exact %s%s' % (info.slice(c.start.byte, c.value_start.byte).rstrip(), pub_of[i],
                                                ''.join(' ' + x for x in explicit_binders(sig)))
        if i in alias_of:
            s, t = alias_of[i]
            c = cmds[i]
            rel = s[len(c.namespace) + 1:] if c.namespace and s.startswith(c.namespace + '.') else s
            return 'alias %s%s := %s' % (rel, suffix if i == tgt else '', next(n for n in cmds[t].names))
        if i == tgt and suffix:
            return renamed(info, i, suffix)
        return leanedit.text(info, i)

    def who(i):
        return '%s (%s)' % (owners[owner_of(cmds[i])] or 'the Blueprint', ', '.join(cmds[i].names) or
                            'line %d' % cmds[i].start.line)

    imported_ns, reg, noted = {}, set(pre_reg), set()
    body, cur = [], None
    for i in order:
        rep = dict(at_root)
        for o, loc in ctx_opens[i]:
            missing = [ns for ns in loc if ns not in reg]
            probe = [ns for ns in missing if ns not in imported_ns]
            if probe:
                found = imported_namespaces(imports_text, probe, scratch)
                imported_ns.update({ns: ns in found for ns in probe})
            missing = [ns for ns in missing if not imported_ns[ns]]
            if not missing:
                continue
            used = [u for u in uses[i] for ns in missing if u.startswith(ns + '.')]
            try:
                if used:
                    raise ValueError
                rep[o] = drop_namespaces(leanedit.text(info, o), missing)
            except ValueError:
                sys.exit('refusing: %s sits under `%s`, which no order can place after %s (declared first by %s)%s'
                         % (who(i), leanedit.text(info, o).strip(), ', '.join(missing),
                            who(first_reg[missing[0]]), '; it uses %s' % ', '.join(used) if used else ''))
            for ns in missing:
                if (o, ns) not in noted:
                    noted.add((o, ns))
                    sys.stderr.write('%s: left %s out of its `%s` for the chunks placed ahead of %s, '
                                     'which do not use it\n' % (owners[owner_of(cmds[i])] or 'the Blueprint', ns,
                                                               leanedit.text(info, o).strip(), who(first_reg[ns])))
        wrap = leanedit.scope_wrap(info, i, replace=rep)
        if wrap != cur:
            if cur is not None:
                body.append(cur[1])
            body.append('\n' + wrap[0])
            cur = wrap
        body += [leanedit.text(info, k) + '\n' for k in attached[i]]
        body.append(text_of(i) + '\n\n')
        reg |= registers(cmds[i])
    if cur is not None:
        body.append(cur[1])
    if tgt is not None:
        body.append('\n' + solution_text(info, tgt, args.target if suffix else cmds[tgt].names[0], suffix,
                                         replace=at_root))
    open(out, 'w', encoding='utf-8').write(header + ''.join(body))
    missing = sorted(n for n in set(stubs) - set(proved) if stubs[n] not in pub_of)
    if missing:
        print('stubs kept (no Part proves them): %s' % ', '.join(missing))
    print('wrote %s (%d stubs replaced)' % (out, len(proved)))
    check_output(out, args.allow_sorry)


def check_output(out, allow_sorry):
    """Elaborate OUT: exit nonzero on an error (q188: a misordered assembly exited 0), and on a
    declaration still using `sorry` (q187: a Blueprint proof left unfinished stayed beside the
    Part's) unless `allow_sorry`, naming each."""
    fin = leaninfo.run(out, use_cache=False)
    if fin.errors:
        sys.exit('%s does not elaborate (kept for inspection; do not submit it):\n' % out + '\n'.join(
            'line %d: %s' % (m.start.line, m.text[:300]) for m in fin.errors[:8]))
    sorried = []
    for m in fin.messages:
        if m.severity == 'warning' and SORRY_WARNING.search(m.text):
            c = next((c for c in fin.commands if c.start.byte <= m.start.byte < c.end.byte), None)
            sorried += c.names if c and c.names else ['line %d' % m.start.line]
    if sorried:
        msg = '%s: still uses `sorry`: %s' % (out, ', '.join(sorried))
        if not allow_sorry:
            sys.exit(msg + ' (no Part proves it; --allow-sorry accepts that)')
        sys.stderr.write(msg + '\n')


if __name__ == '__main__':
    main()
