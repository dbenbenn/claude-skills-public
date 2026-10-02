#!/usr/bin/env python3
"""Assemble one Lean file from a Blueprint (definitions + `sorry` lemmas) and Part files proving them.

usage: assemble_blueprint.py BLUEPRINT.lean OUT.lean PART.lean [PART.lean ...]

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
file. Stubs no Part proves are kept. Run `lake env lean OUT.lean` and `#print axioms` afterwards.
"""
import heapq
import os
import re
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))  # p2mlib
from p2mlib import leanedit, leaninfo  # noqa: E402
from p2mlib.leantext import header_end, strip  # noqa: E402

STRUCTURAL = {'namespace', 'section', 'noncomputableSection', 'end', 'eoi', 'open', 'variable',
              'universe', 'include', 'omit', 'set_option'}


def imports(text):
    return re.findall(r'^import\s+(\S+)', strip(text[:header_end(text)]), re.M)


def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    bpf, out, parts = sys.argv[1], sys.argv[2], sys.argv[3:]
    files = [bpf] + parts
    texts = [open(f, encoding='utf-8').read() for f in files]
    owners = [None] + [os.path.splitext(os.path.basename(p))[0] for p in parts]
    bp_mods = {m for t in texts[1:] for m in imports(t) if m.endswith('Blueprint')}
    hdr = []
    for t in texts:
        hdr += [m for m in imports(t) if m not in bp_mods and m not in hdr]
    header = ''.join('import %s\n' % m for m in hdr)
    concat, spans = header, []
    for t in texts:
        concat += 'section\n'
        a = len(concat.encode())
        concat += t[header_end(t):].rstrip('\n') + '\n'
        spans.append((a, len(concat.encode())))
        concat += 'end\n'
    fd, tmp = tempfile.mkstemp(suffix='.lean', prefix='.assemble_', dir=os.path.dirname(os.path.abspath(out)))
    with os.fdopen(fd, 'w', encoding='utf-8') as f:
        f.write(concat)
    try:
        info = leaninfo.run(tmp, use_cache=False)
    finally:
        os.remove(tmp)
    if info.errors:
        sys.exit('the Blueprint with its Parts does not elaborate:\n' + '\n'.join(
            'line %d: %s' % (m.start.line, m.text[:300]) for m in info.errors[:8]))

    def owner_of(c):
        return next((k for k, (a, b) in enumerate(spans) if a <= c.start.byte < b), None)

    cmds = info.commands
    declares = {d.command for d in info.decls if d.command is not None}
    items = [c.index for c in cmds if owner_of(c) is not None and c.short_kind not in STRUCTURAL
             and (c.index in declares or c.names or c.decl_kind)]
    item_set = set(items)
    # other commands go with the next declaration of their file (else the previous one)
    attached = {i: [] for i in items}
    for c in cmds:
        k = owner_of(c)
        if k is None or c.index in item_set or c.short_kind in STRUCTURAL:
            continue
        nxt = [i for i in items if owner_of(cmds[i]) == k and i > c.index]
        prv = [i for i in items if owner_of(cmds[i]) == k and i < c.index]
        if nxt or prv:
            attached[nxt[0] if nxt else prv[-1]].append(c.index)

    def value(i):
        c = cmds[i]
        return info.slice(c.value_start.byte, c.end.byte) if c.value_start else ''

    stubs = {n: c.index for c in cmds if owner_of(c) == 0 and c.decl_kind == 'theorem'
             for n in c.names if re.fullmatch(r':=\s*(by\s+)?sorry\s*', value(c.index))}
    proved = {}                                    # stub full name -> target command
    for i in items:
        c = cmds[i]
        if owner_of(c) and c.decl_kind == 'theorem' and c.namespace:
            for n in c.names:
                stub = c.namespace.rsplit('.', 1)[0] + n[len(c.namespace):] if n.startswith(c.namespace + '.') else None
                if stub in stubs:
                    proved[stub] = i
    alias_of = {stubs[s]: (s, t) for s, t in proved.items()}

    cmd_of = {d.name: d.command for d in info.decls}
    deps = {i: set() for i in items}
    for d in info.decls:
        if d.command in deps and d.command not in alias_of:
            deps[d.command] |= {cmd_of[u] for u in d.uses_local if cmd_of.get(u) in deps} - {d.command}
    for i, (s, t) in alias_of.items():
        deps[i] = {t}
    for k in range(1, len(files)):                 # a Part keeps its own order
        mine = [i for i in items if owner_of(cmds[i]) == k]
        for x, y in zip(mine, mine[1:]):
            deps[y].add(x)
    # preference: the Blueprint's order; a Part item just before the stub of its Part's next target
    bitems = [i for i in items if owner_of(cmds[i]) == 0]
    bpos = {i: n for n, i in enumerate(bitems)}
    target_stub = {t: stubs[s] for s, t in proved.items()}
    pref = {}
    for i in items:
        if owner_of(cmds[i]) == 0:
            pref[i] = (2 * bpos[i] + 1, i)
        else:
            later = [j for j in items if j >= i and owner_of(cmds[j]) == owner_of(cmds[i]) and j in target_stub]
            pref[i] = (2 * bpos[target_stub[later[0]]] if later else 2 * len(bitems), i)
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
    if len(order) < len(items):
        stuck = [', '.join(cmds[i].names) or str(i) for i in items if i not in set(order)]
        sys.exit('dependency cycle among: %s (a Part helper using the stub its own Part proves?)'
                 % '; '.join(stuck[:12]))

    def text_of(i):
        if i in alias_of:
            s, t = alias_of[i]
            c = cmds[i]
            rel = s[len(c.namespace) + 1:] if c.namespace and s.startswith(c.namespace + '.') else s
            return 'alias %s := %s' % (rel, next(n for n in cmds[t].names))
        return leanedit.text(info, i)

    body, cur = [], None
    for i in order:
        wrap = leanedit.scope_wrap(info, i)
        if wrap != cur:
            if cur is not None:
                body.append(cur[1])
            body.append('\n' + wrap[0])
            cur = wrap
        body += [leanedit.text(info, k) + '\n' for k in attached[i]]
        body.append(text_of(i) + '\n\n')
    if cur is not None:
        body.append(cur[1])
    open(out, 'w', encoding='utf-8').write(header + ''.join(body))
    missing = sorted(set(stubs) - set(proved))
    if missing:
        print('stubs kept (no Part proves them): %s' % ', '.join(missing))
    print('wrote %s (%d stubs replaced)' % (out, len(proved)))


if __name__ == '__main__':
    main()
