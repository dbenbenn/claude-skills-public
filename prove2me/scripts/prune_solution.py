#!/usr/bin/env python3
"""Delete the declarations an assembled solution never uses, before submitting it.

A solution built by concatenating modules carries lemmas its target does not touch. That is
not merely untidy:

  * a reader cannot tell which lemmas the proof depends on, and neither can you months later;
  * an unused copy of a *published* theorem looks like a missing graph edge, and importing it
    to "fix" that asserts a dependency the proof does not have — a false edge, which is worse
    than a missing one, and it still compiles so nothing catches it.

What counts as used is reachability from `solution` in the file's own call graph — not being
referenced somewhere, since a lemma referenced only by another unused lemma is still unused.

DANGER, and the reason this script never prunes on its own judgement alone: **unused by name is
not unused**. A `@[simp]` lemma is applied by `simp` without being named, an `instance` is found
by typeclass resolution, `@[ext]`/`@[norm_cast]`/`@[elab_as_elim]` and friends register a
declaration with a tactic or the elaborator. Any of those can be load-bearing while no proof
mentions it. So every attributed declaration, every `instance`, and everything reachable from
them is treated as a root, and the result MUST be compiled before it is submitted. Pass
--check to have this script do that, and do not skip it.

usage:
    prune_solution.py FILE [-o OUT] [--check] [--dry]

    --check  elaborate the pruned file with `lake env lean` (run from $P2M_WORKSPACE)
    --dry    report what would go, write nothing
"""
import argparse
import os
import re
import subprocess
import sys
from collections import defaultdict

KINDS = r'(?:lemma|theorem|def|abbrev|instance|structure|inductive|class)'
# an attribute may sit on the declaration's own line (`@[simp] theorem foo …`); such a
# declaration is attributed exactly as if the attribute were on the line above
DECL = re.compile(r'^(?P<attr>(?:@\[[^\]]*\]\s*)*)'
                  r'(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)'
                  r'(?P<kind>%s)\s+(?P<name>[A-Za-z_][A-Za-z0-9_.\'!?]*)' % KINDS)
TOP = re.compile(r'^(?:@\[|/--|/-!|%s|private|protected|noncomputable|partial|unsafe|end\b|'
                 r'namespace\b|section\b|open\b|variable\b|universe\b|attribute\b|local\b)' % KINDS)


def parse(lines):
    """[(name, kind, start, end, attributed)] for top-level declarations, in file order.

    `start` includes any attribute lines and doc comment immediately above.
    """
    heads = []
    for i, l in enumerate(lines):
        m = DECL.match(l)
        if m:
            heads.append((i, m.group('name'), m.group('kind'), bool(m.group('attr'))))
    out = []
    for k, (i, name, kind, inline_attr) in enumerate(heads):
        j = i + 1
        while j < len(lines) and not TOP.match(lines[j]):
            j += 1
        while j - 1 > i and lines[j - 1].strip() == '':
            j -= 1
        s = i
        attributed = inline_attr
        # walk back over blank lines, a doc comment, and any attribute lines
        while s - 1 >= 0:
            prev = lines[s - 1].rstrip()
            if prev.strip() == '':
                s -= 1
                continue
            if prev.endswith('-/'):
                d = s - 1
                while d >= 0 and not lines[d].lstrip().startswith(('/--', '/-!')):
                    d -= 1
                if d >= 0 and lines[d].lstrip().startswith('/--'):
                    s = d
                    continue
                break
            if prev.lstrip().startswith('@['):
                attributed = True
                s -= 1
                continue
            # a scoping prefix (`open Classical in`, `variable (m) in`, `set_option … in`)
            # belongs to the declaration: left behind, it would attach to whatever follows
            if re.match(r'(open|variable|set_option|omit|include)\b.*\bin$', prev.strip()):
                s -= 1
                continue
            break
        out.append((name, kind, s, j, attributed))
    return out


def callgraph(lines, decls):
    names = {d[0] for d in decls}
    g = defaultdict(set)
    # a reference may be namespace-qualified (`Chou.Lib.foo` for a `foo` declared inside
    # `namespace Chou.Lib`), so allow a dotted prefix. Excluding a preceding '.' — the obvious
    # way to stop `Foo.bar` matching `bar` — makes every qualified call invisible, and the
    # analysis then reports live code as dead.
    pats = {n: re.compile(r"(?<![A-Za-z0-9_'])(?:[A-Za-z_][A-Za-z0-9_']*\.)*%s(?![A-Za-z0-9_'])"
                          % re.escape(n)) for n in names}
    for name, kind, s, e, _ in decls:
        body = '\n'.join(lines[s:e])
        for other in names:
            if other != name and pats[other].search(body):
                g[name].add(other)
    return g


def prune(text, verbose=True):
    lines = text.split('\n')
    decls = parse(lines)
    if not any(d[0] == 'solution' for d in decls):
        raise SystemExit('no `solution` declaration — refusing to prune')

    roots = {'solution'}
    for name, kind, s, e, attributed in decls:
        # implicit users: tactics and typeclass resolution find these without naming them
        if attributed or kind in ('instance', 'structure', 'inductive', 'class'):
            roots.add(name)

    g = callgraph(lines, decls)
    seen = set(roots)
    stack = list(roots)
    while stack:
        n = stack.pop()
        for m in g.get(n, ()):
            if m not in seen:
                seen.add(m)
                stack.append(m)

    doomed = [d for d in decls if d[0] not in seen]
    if verbose:
        kept = len(decls) - len(doomed)
        print('declarations: %d   kept: %d   unused: %d' % (len(decls), kept, len(doomed)))
        for name, kind, s, e, _ in doomed:
            print('   - %-58s %s, %d lines' % (name[:58], kind, e - s))
    keep_mask = [True] * len(lines)
    for _, _, s, e, _ in doomed:
        for i in range(s, e):
            keep_mask[i] = False
    out = '\n'.join(l for i, l in enumerate(lines) if keep_mask[i])
    return out, doomed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('file')
    ap.add_argument('-o', '--out')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()

    text = open(a.file, encoding='utf-8').read()
    n0 = len(text.split('\n'))
    out, doomed = prune(text)
    n1 = len(out.split('\n'))
    print('%d -> %d lines (%d removed)' % (n0, n1, n0 - n1))
    if a.dry:
        return
    dest = a.out or a.file
    open(dest, 'w', encoding='utf-8').write(out)
    print('wrote %s' % dest)

    if a.check:
        ws = os.environ.get('P2M_WORKSPACE') or os.path.expanduser('~/claude/prove2me_workspace')
        rel = os.path.relpath(os.path.abspath(dest), ws)
        p = subprocess.run(['lake', 'env', 'lean', rel], cwd=ws,
                           capture_output=True, text=True)
        errs = [l for l in (p.stdout + p.stderr).split('\n') if ': error:' in l]
        if errs:
            print('COMPILE FAILED — the prune removed something that was load-bearing:')
            for l in errs[:10]:
                print('   ', l[:200])
            sys.exit(1)
        print('compiles clean')


if __name__ == '__main__':
    main()
