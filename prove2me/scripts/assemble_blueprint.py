#!/usr/bin/env python3
"""Assemble one Lean file from a Blueprint (definitions + `sorry` lemmas) and Part files proving them.

usage: assemble_blueprint.py BLUEPRINT.lean OUT.lean PART.lean [PART.lean ...]

The parallel-prover pattern (F-amenability child, Lodha–Moore Lemma 5.6, 2026-10-02): a Blueprint
states every lemma with `sorry` and proves the main theorem from them; each prover writes
`Part<X>.lean` (`import <Blueprint module>`, `namespace <NS>.Part<X>`) restating some Blueprint
lemmas verbatim with proofs. This script:

* splits each Part body into chunks, one per target lemma: the helpers since the previous target,
  then the target. A *target* is a theorem of the Part whose name is also a `sorry` lemma of the
  Blueprint;
* deletes each Blueprint stub and puts in its place the chunk (nested `namespace Part<X>`, with
  the Part's own `open` lines repeated) followed by `alias foo := Part<X>.foo`, so later
  Blueprint definitions and lemmas see a real proof under the Blueprint name;
* merges the imports (the Blueprint's, plus the Parts' other than the Blueprint itself).

Helpers therefore land just before the lemma they serve, after every Blueprint definition that
lemma's statement uses. A helper that needs a later Blueprint definition must move in its Part
file (below the targets that come before that definition). Stubs without a Part proof are kept.
Run `lake env lean OUT.lean` and `#print axioms` afterwards.
"""
import os, re, sys

HEAD = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:private |protected |noncomputable )*"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|alias)\s+([^\s(:{\[]+)")


def body_lines(lines, ns):
    s = next(i for i, l in enumerate(lines) if re.match(r'^namespace %s\s*$' % re.escape(ns), l))
    e = max(i for i, l in enumerate(lines) if re.match(r'^end %s\s*$' % re.escape(ns), l))
    return lines[:s], lines[s + 1:e]


def decls(lines):
    """[(name, kind, start, end)] of top-level declarations; start includes the doc comment and
    attribute lines above; end stops at the next declaration (with its doc comment) or the next
    top-level command, with trailing blank lines dropped."""
    heads = [(i, m.group(2), m.group(1)) for i, l in enumerate(lines) for m in [HEAD.match(l)] if m]
    starts = []
    for i, _, _ in heads:
        s = i
        while s > 0 and (lines[s - 1].startswith('@[') or lines[s - 1].rstrip().endswith('-/')):
            if lines[s - 1].startswith('@['):
                s -= 1
                continue
            d = s - 1
            while d > 0 and not lines[d].lstrip().startswith('/-'):
                d -= 1
            if not lines[d].lstrip().startswith('/--'):
                break   # a section comment `/-! -/` or plain `/- -/` is not attached
            s = d
        starts.append(s)
    out = []
    for k, (i, name, kind) in enumerate(heads):
        e = starts[k + 1] if k + 1 < len(heads) else len(lines)
        for j in range(i + 1, e):
            if re.match(r'^(open|section|end|namespace|variable|set_option|/-!|#)\b', lines[j]) or \
               lines[j].startswith('/-!'):
                e = j
                break
        while e - 1 > i and lines[e - 1].strip() == '':
            e -= 1
        out.append((name, kind, starts[k], e))
    return out


def stub_names(bp):
    """Blueprint theorems whose proof is `sorry`."""
    names = []
    for name, kind, s, e in decls(bp):
        if kind in ('theorem', 'lemma'):
            text = '\n'.join(bp[s:e])
            if re.search(r':=\s*(by\s+)?sorry\s*$', text.strip()):
                names.append(name)
    return names


TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")


def strip_comments(text):
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
    return re.sub(r'--[^\n]*', ' ', text)


def mentions(text):
    """Every name component and every dotted suffix mentioned outside comments."""
    out = set()
    for tok in TOK.findall(strip_comments(text)):
        parts = tok.split('.')
        for k in range(len(parts)):
            out.add('.'.join(parts[k:]))
    return out


def split_items(lines):
    """(header, [(name, kind, lines)], footer): declarations with everything up to the next one."""
    ds = decls(lines)
    if not ds:
        return lines, [], []
    header = lines[:ds[0][2]]
    items = []
    for k, (name, kind, s, e) in enumerate(ds):
        nxt = ds[k + 1][2] if k + 1 < len(ds) else e
        items.append((name, kind, lines[s:nxt] if k + 1 < len(ds) else lines[s:e]))
    return header, items, lines[ds[-1][3]:]


def main():
    bpf, out, parts = sys.argv[1], sys.argv[2], sys.argv[3:]
    bp = open(bpf, encoding='utf-8').read().split('\n')
    stubs = set(stub_names(bp))
    ns_root = next(m.group(1) for l in bp for m in [re.match(r'^namespace (\S+)', l)] if m)
    imports = [l for l in bp if l.startswith('import ')]
    header, bitems, footer = split_items([l for l in bp if not l.startswith('import ')])
    # nodes: (key, owner, name, lines, pref); owner None = Blueprint, else the Part
    nodes = []
    proved = {}
    part_opens = {}
    for pf in parts:
        part = os.path.splitext(os.path.basename(pf))[0]
        lines = open(pf, encoding='utf-8').read().split('\n')
        pre, body = body_lines(lines, '%s.%s' % (ns_root, part))
        imports += [l for l in lines if l.startswith('import ') and 'Blueprint' not in l and l not in imports]
        part_opens[part] = [l for l in pre + body if re.match(r'^open\s', l) and not l.rstrip().endswith(' in')]
        _, pitems, _ = split_items([l for l in body if l not in part_opens[part]])
        for name, kind, ls in pitems:
            if name in stubs and kind in ('theorem', 'lemma'):
                proved[name] = part
        nodes += [(part, name, kind, ls) for name, kind, ls in pitems]
    bnodes = []
    for name, kind, ls in bitems:
        if name in proved and kind in ('theorem', 'lemma'):
            ls = ['alias %s := %s.%s' % (name, proved[name], name), '']
        bnodes.append((None, name, kind, ls))
    allnodes = bnodes + nodes
    # preferred position: Blueprint index; a Part item takes the index of the stub of the next
    # target in its file (so helpers sit just before the lemma they serve)
    bindex = {n[1]: i for i, n in enumerate(bnodes)}
    pref = []
    for i, (owner, name, kind, ls) in enumerate(allnodes):
        if owner is None:
            pref.append((i * 2 + 1, i))
        else:
            j = i
            while j < len(allnodes) and not (allnodes[j][0] == owner and allnodes[j][1] in proved
                                             and proved[allnodes[j][1]] == owner):
                j += 1
            tgt = allnodes[j][1] if j < len(allnodes) else None
            pref.append((bindex.get(tgt, len(bnodes)) * 2, i))
    # provides: a name is provided by the Blueprint item, or by the Part item of that name
    provides = {}
    for i, (owner, name, kind, ls) in enumerate(allnodes):
        for key in {name, name.split('.')[-1]}:
            provides.setdefault(key, []).append(i)
    deps = [set() for _ in allnodes]
    for i, (owner, name, kind, ls) in enumerate(allnodes):
        text = '\n'.join(ls)
        if owner is None and name in proved:
            deps[i] |= {j for j, n in enumerate(allnodes) if n[0] == proved[name] and n[1] == name}
            continue
        for m in mentions(text):
            for j in provides.get(m, []):
                if j == i:
                    continue
                # a Part item never depends on the alias of its own target name, and a Blueprint
                # item mentioning a proved stub depends on the alias, not the Part item
                if allnodes[j][0] is not None and owner is None:
                    continue
                # a Part imports only the Blueprint: never another Part's helpers (same-named
                # helpers in two Parts made a cycle)
                if owner is not None and allnodes[j][0] not in (None, owner):
                    continue
                if owner is not None and allnodes[j][0] is None and allnodes[j][1] in proved \
                        and proved[allnodes[j][1]] == owner and any(n[0] == owner and n[1] == allnodes[j][1]
                                                                    for n in allnodes):
                    continue
                deps[i].add(j)
        # the Part's own order is kept: a Part item follows the previous item of its Part
        if owner is not None:
            prev = [j for j in range(i) if allnodes[j][0] == owner]
            if prev:
                deps[i].add(prev[-1])
    import heapq
    indeg = [len(d) for d in deps]
    users = [[] for _ in allnodes]
    for i, d in enumerate(deps):
        for j in d:
            users[j].append(i)
    heap = [(pref[i], i) for i in range(len(allnodes)) if indeg[i] == 0]
    heapq.heapify(heap)
    order = []
    while heap:
        _, i = heapq.heappop(heap)
        order.append(i)
        for u in users[i]:
            indeg[u] -= 1
            if indeg[u] == 0:
                heapq.heappush(heap, (pref[u], u))
    if len(order) < len(allnodes):
        stuck = [allnodes[i][1] for i in range(len(allnodes)) if i not in set(order)]
        sys.exit('dependency cycle among: %s' % ', '.join(stuck[:20]))
    body, cur = [], None
    for i in order:
        owner, name, kind, ls = allnodes[i]
        if owner != cur:
            if cur is not None:
                body += ['end %s' % cur, '']
            if owner is not None:
                body += ['namespace %s' % owner] + part_opens[owner]
            cur = owner
        body += ls
    if cur is not None:
        body += ['end %s' % cur, '']
    missing = sorted(stubs - set(proved))
    if missing:
        print('stubs kept (no Part proves them): %s' % ', '.join(missing))
    open(out, 'w', encoding='utf-8').write('\n'.join(imports + header + body + footer) + '\n')
    print('wrote %s (%d stubs replaced)' % (out, len(proved)))


if __name__ == '__main__':
    main()
