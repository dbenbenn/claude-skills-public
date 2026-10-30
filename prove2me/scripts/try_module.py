#!/usr/bin/env python3
"""Compile one ported module as is and with the transparency option, and list the errors of each.

usage: try_module.py FILE [--show LINE,...] [--keep OUT]

For a category-theory or homological-algebra port, try this first on each failing module (oaiq-116).
Errors full of `simp made no progress` / `rewrite failed` on `comp_f`, `ShiftedHom`, `Cocycle` or
`single…` lemmas are usually the "not type-correct under the `implicit` transparency level" check,
not API drift. The option is `set_option backward.isDefEq.respectTransparency false`, inserted at
module scope right after the imports (a `set_option` inside `namespace OAI` ends with it). FILE is
never changed: the copy with the option goes to a temporary file, or to OUT with --keep.

Both versions compile from the prove2me workspace with the pipeline's own flags (`lake env lean -j1
-DautoImplicit=false`): a `-j1` build can hit heartbeats that an in-place `lake build` does not.
They run one after the other through the lean-cap wrapper (p2mlib.lean_cap_first). For each
version it prints the first line of every error, with line numbers in FILE's own numbering, and the
full message for the lines --show names. It ends by naming the version with fewer errors (or a tie). Where the
option breaks later steps ("No goals to be solved" after a `rfl`/`erw`), scope it per declaration
with `set_option ... false in`. Folded in from oaiq-116's tools/try_module.py.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))  # p2mlib
from p2mlib import lean_cap_first  # noqa: E402
from p2mlib.leantext import header_end  # noqa: E402

OPT = 'set_option backward.isDefEq.respectTransparency false'
FLAGS = ['-j1', '-DautoImplicit=false']          # what oai_build_modules and carve_measure use


def with_option(text):
    """(text with OPT on its own line right after the last import, the option's 1-based line), or
    (text, None) when the file already sets it."""
    if re.search(r'^\s*' + re.escape(OPT) + r'\s*$', text, re.M):
        return text, None
    head = text[:header_end(text)].split('\n')
    last = max((i for i, l in enumerate(head) if l.startswith('import ')), default=-1)
    lines = text.split('\n')
    lines.insert(last + 1, OPT)
    return '\n'.join(lines), last + 2


def errors(log):
    """[(line, full message)] of the errors in a Lean log (warnings and lean-cap lines dropped)."""
    out = []
    for part in re.split(r'(?m)^(?=\S+:\d+:\d+: )', log):
        m = re.match(r'\S+:(\d+):\d+: error', part)
        if m:
            out.append((int(m.group(1)), '\n'.join(l for l in part.rstrip('\n').split('\n')
                                                   if not l.startswith('lean-cap:'))))
    return out


def compile_(path, ws, run=subprocess.run):
    env = dict(os.environ)
    lean_cap_first(env)
    r = run(['lake', 'env', 'lean'] + FLAGS + [path], cwd=ws, env=env, capture_output=True, text=True)
    return r.stdout + r.stderr


def report(label, errs, show):
    print('%s: %d error%s' % (label, len(errs), '' if len(errs) == 1 else 's'))
    for line, msg in errs:
        if line in show:
            print('  line %d of FILE:\n%s\n=====' % (line, msg[:4000]))
        else:
            print('  %d: %s' % (line, msg.split('\n')[0].split(': ', 1)[-1][:160]))


def try_module(path, ws=None, run=subprocess.run, show=(), keep=None):
    """Compile FILE as is and with OPT; print both error lists. Returns {'as is': errs, 'with option':
    errs or None (already set), 'fewer': 'as is' | 'with option' | 'tie'}."""
    if ws is None:
        from p2mlib.workspace import workspace
        ws = workspace()
    path = os.path.abspath(path)
    show = set(show)
    res = {'as is': errors(compile_(path, ws, run))}
    report('as is', res['as is'], show)
    text, at = with_option(open(path, encoding='utf-8').read())
    if at is None:
        print('the file already sets the option; nothing to compare')
        res.update({'with option': None, 'fewer': 'as is'})
        return res
    tmpd = None
    if keep:
        out = os.path.abspath(keep)
    else:
        tmpd = tempfile.mkdtemp(prefix='try_module_')
        out = os.path.join(tmpd, os.path.basename(path))
    try:
        open(out, 'w', encoding='utf-8').write(text)
        opt = [(l - 1 if l > at else l, m) for l, m in errors(compile_(out, ws, run))]
    finally:
        if tmpd:
            shutil.rmtree(tmpd, ignore_errors=True)
    res['with option'] = opt
    report('with the option', opt, show)
    n0, n1 = len(res['as is']), len(opt)
    res['fewer'] = 'with option' if n1 < n0 else 'as is' if n0 < n1 else 'tie'
    print('%s%s' % ({'with option': 'fewer errors with the option (%d vs %d as is)' % (n1, n0),
                     'as is': 'fewer errors as is (%d vs %d with the option)' % (n0, n1),
                     'tie': 'the same number of errors either way (%d); compare them' % n0}[res['fewer']],
                    '; copy kept at %s' % out if keep else ''))
    return res


def main(argv):
    if not argv or argv[0].startswith('--'):
        sys.exit(__doc__)
    show, keep = set(), None
    if '--show' in argv:
        show = {int(x) for x in argv[argv.index('--show') + 1].split(',') if x}
    if '--keep' in argv:
        keep = argv[argv.index('--keep') + 1]
    try_module(argv[0], show=show, keep=keep)


if __name__ == '__main__':
    main(sys.argv[1:])
