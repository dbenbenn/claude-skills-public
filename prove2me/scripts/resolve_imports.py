#!/usr/bin/env python3
"""Make a merged solution file self-contained: import what is published, inline what is not.

usage: resolve_imports.py BODY.lean OUT.lean --src DIR [--ns QFS] [--import NAME ...]
                          [--defs-prefix Def_QFS_] [--max-iter 15]

A development written as a Lean project uses lemmas from its own modules. A prove2.me solution
may import only definition bundles, published theorems and Mathlib, so every lemma the merged
file mentions must be either imported (`import Theorems.Thm_<NS>_<name>`, when that theorem is
published AND Proved: importing an Open theorem turns the submission into a reduction) or copied
in verbatim from its source module. This script does that by compiling in the workspace and
reading the "Unknown identifier" errors, one round at a time, until none are left.

BODY.lean is the merged development WITHOUT import lines (see merge.py; wrap each module in its own
`section ... end` before merging -- module-level `open`s otherwise leak into later modules, which
silently changes which lemma a bare name like `inv_zero` resolves to). The header written here
imports every bundle `Definitions/<defs-prefix>*.lean` in the workspace; prune the unused ones
afterwards. Inlined declarations go in their own `namespace <NS> ... end <NS>` block, with the
`open`s INSIDE the namespace so they end with it (the same leak). Then run prune_solution.py
--check and submit_solution.py as usual.

Lessons encoded (both cost a debugging round when this was a one-off script for QFS, 2026-09-26):
the opens leak above; and a declaration extractor that ran its command-line code at import time.
"""
import argparse, glob, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from p2m import call
from prune_solution import _workspace

START = re.compile(r'^(theorem|lemma|def|noncomputable|/--|/-!|end\b|namespace|section|@\[|instance|'
                   r'abbrev|structure|open|variable|private|protected)')


def extract(path, name):
    """The text of declaration `name` in `path`, with a doc comment directly above it."""
    L = open(path, encoding='utf-8').read().split('\n')
    for i, l in enumerate(L):
        if re.match(r'^(private )?(theorem|lemma) ' + re.escape(name) + r'(\s|$)', l):
            a = i
            if a > 0 and L[a - 1].strip().endswith('-/'):
                j = a - 1
                while not L[j].lstrip().startswith('/--'):
                    j -= 1
                a = j
            b = i + 1
            while b < len(L) and not START.match(L[b]):
                b += 1
            return '\n'.join(L[a:b]).rstrip() + '\n'
    return None


def find_src(src_dir, name):
    for f in sorted(glob.glob(os.path.join(src_dir, '**', '*.lean'), recursive=True)):
        if re.search(r'^(private )?(theorem|lemma) ' + re.escape(name) + r'(\s|$)',
                     open(f, encoding='utf-8').read(), re.M):
            return f
    return None


def proved(ns, name):
    for _ in range(3):  # lookups under load have silently returned nothing; retry
        try:
            r = call('GET', '/theorems?theorem_name=%s.%s' % (ns, name)).get('theorems') or []
            hit = [t for t in r if t.get('theorem_name') == '%s.%s' % (ns, name)]
            return bool(hit) and hit[0].get('status') == 'Proved'
        except Exception:
            continue
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('body'); ap.add_argument('out')
    ap.add_argument('--src', required=True, help='source tree of the development')
    ap.add_argument('--ns', default='QFS')
    ap.add_argument('--import', dest='imports', action='append', default=[])
    ap.add_argument('--defs-prefix', default=None)
    ap.add_argument('--max-iter', type=int, default=15)
    a = ap.parse_args()
    ws = _workspace()
    prefix = a.defs_prefix or 'Def_%s_' % a.ns
    imports, inline = list(a.imports), []
    body = open(a.body, encoding='utf-8').read()
    scratch = os.path.join(ws, 'scratch', 'resolve_imports_%d.lean' % os.getpid())

    def build():
        hdr = ['import Definitions.%s' % os.path.basename(f)[:-5]
               for f in sorted(glob.glob(os.path.join(ws, 'Definitions', prefix + '*.lean')))]
        hdr += ['import Theorems.Thm_%s_%s' % (a.ns, n) for n in imports] + ['import Mathlib', '']
        inl = ''.join(extract(s, n) + '\n' for s, n in inline)
        txt = '\n'.join(hdr)
        if inl:
            txt += ('\n/-! Lemmas of the development that are not published, copied verbatim. -/\n\n'
                    'namespace %s\n\nopen Real Set Metric MeasureTheory ENNReal Filter Topology\n'
                    'open scoped NNReal\n\n' % a.ns + inl + 'end %s\n' % a.ns)
        return txt + '\n' + body

    for it in range(a.max_iter):
        txt = build()
        open(scratch, 'w', encoding='utf-8').write(txt)
        out = subprocess.run(['lake', 'env', 'lean', scratch], cwd=ws, capture_output=True, text=True).stdout
        unk = sorted(set(re.findall(r'Unknown (?:identifier|constant) `(?:%s\.)?([^`]+)`' % a.ns, out)))
        errs = [l for l in out.split('\n') if 'error' in l]
        print('round %d: %d errors, unknown %s' % (it, len(errs), unk), flush=True)
        if not unk:
            open(a.out, 'w', encoding='utf-8').write(txt)
            os.remove(scratch)
            if errs:
                print('\n'.join(errs[:20]))
                sys.exit('remaining errors are not unknown names; fix them by hand')
            print('wrote %s: %d imports, %d inlined' % (a.out, len(imports), len(inline)))
            return
        for n in unk:
            if os.path.exists(os.path.join(ws, 'Theorems', 'Thm_%s_%s.lean' % (a.ns, n))) and proved(a.ns, n):
                imports.append(n); print('  import', n)
            else:
                s = find_src(a.src, n)
                if not s:
                    sys.exit('cannot find a source for %s' % n)
                inline.insert(0, (s, n)); print('  inline', n, os.path.relpath(s, a.src))
    sys.exit('gave up after %d rounds' % a.max_iter)


if __name__ == '__main__':
    main()
