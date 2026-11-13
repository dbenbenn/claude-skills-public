#!/usr/bin/env python3
"""Re-record lean_fixtures/<Name>.json and <Name>.parse.json from the current LeanInfo.

usage: python3 tests/record_fixtures.py [NAME ...]   (default: every fixture test_leaninfo replays)
       python3 tests/record_fixtures.py carve       (the carver's CarveDev development, test_carve)
       python3 tests/record_fixtures.py assemble    (assemble/*.lean, parse-only, test_assemble_blueprint)

Run after changing lean/LeanInfo.lean, then read `git diff tests/lean_fixtures`: the diff is the
change in what the tool reports, and test_tool_reproduces_recording pins it."""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import leaninfo  # noqa: E402

FIX = os.path.join(HERE, 'lean_fixtures')
# the CarveDev development's root modules (test_carve.test_tools_reproduce_the_recordings uses them too)
CARVE_ROOTS = ['CarveDev.Top', 'CarveDev.ShadowA', 'CarveDev.ShadowB', 'CarveDev.ShadowC', 'CarveDev.ShadowD',
               'CarveDev.SimpRflB', 'CarveDev.DupTop', 'CarveDev.SimpTop',
               'CarveDev.NotaVar', 'CarveDev.CoeLocal', 'CarveDev.UnivMax', 'CarveDev.LocalFor',
               'CarveDev.NamedNota', 'CarveDev.ExpUse', 'CarveDev.AttrReg', 'CarveDev.InstPriv']
REPLAYED = ['Structure', 'Broken', 'Notation', 'Rewire', 'Audit', 'Scope', 'Alias', 'Variable', 'ScopedVariable']


def record(name):
    for parse_only, suffix in ((False, ''), (True, '.parse')):
        path = os.path.join(FIX, name + '.lean')
        data = leaninfo.raw(path, parse_only=parse_only)
        data.pop('build_ms', None)            # a timing, never the same twice
        data['file'] = name + '.lean'
        with open(os.path.join(FIX, name + suffix + '.json'), 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=1, sort_keys=True)
        print('recorded', name + suffix)


def record_assemble():
    """Record lean_fixtures/assemble/<Name>.parse.json (parse-only) for every <Name>.lean there: the
    copy-header Blueprint and Parts test_assemble_blueprint replays without Lean."""
    d = os.path.join(FIX, 'assemble')
    for f in sorted(os.listdir(d)):
        if f.endswith('.lean'):
            data = leaninfo.raw(os.path.join(d, f), parse_only=True)
            data.pop('build_ms', None)
            data['file'] = f
            with open(os.path.join(d, f[:-5] + '.parse.json'), 'w', encoding='utf-8') as out:
                json.dump(data, out, ensure_ascii=False, indent=1, sort_keys=True)
            print('recorded assemble/' + f[:-5] + '.parse')


def record_carve():
    """Compile lean_fixtures/carve/CarveDev (core Lean only) into a scratch directory, then record
    DeclGraph's output and each module's LeanInfo (parse-only, --idents) beside the sources."""
    import tempfile
    from p2mlib import carve
    src = os.path.join(FIX, 'carve')
    with tempfile.TemporaryDirectory() as d:
        for rel in carve.record_fixture(src, 'CarveDev', CARVE_ROOTS, os.path.join(d, 'olean'), src):
            print('recorded carve/' + rel)


if __name__ == '__main__':
    for n in sys.argv[1:] or REPLAYED:
        record_carve() if n == 'carve' else record_assemble() if n == 'assemble' else record(n)
