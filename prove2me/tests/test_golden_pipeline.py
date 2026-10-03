"""Pipeline regression on golden files (layer 3): rebuild a real, tricky solution from its
development modules and compare with the solution the platform ACCEPTED (fetched once into
tests/golden/<case>/expected.lean; never refetched).

Each case directory holds src/*.lean (the check module and its Solutions dependencies, imports
renamed to Solutions.Golden.<case>.*), expected.lean and meta.json (target, check module, the
accepted submission id, why the case is tricky, and `status`: exact | partial | xfail).

`partial` is for a solution finished by hand beyond what any pipeline can do: the rebuild must
compile and import exactly `theorem_imports` (its graph edges), and is not compared further.

`exact` means: the rebuild equals the accepted file, ignoring whitespace-only lines (blank lines
mean nothing to Lean and the pruner's spacing is not under test) and the order of the `import`
lines (a set: they are the graph edges) and the lines that only wrap `theorem solution` in its
scope (`section`, `open`, `end`: how the builder writes them is not under test, that they suffice
is the compile check), after deleting from the accepted
file the declarations listed in `dropped_since_accepted` -- dead code the pruner of the day kept and
a better one removes (each with the reason). An unlisted difference fails: a new deletion is either
a regression or a pruning gain, and the case says which.

The pipeline is what submit_all.py runs: build_solutions.build (merge, rewire, prune), then
prune_solution.py --check. Needs the Lean workspace (published Theorems/Definitions are immutable,
so relying on them is stable): run with P2M_LEAN=1."""
import difflib
import json
import os
import re
import shutil
import subprocess
import sys

import pytest

from conftest import SCRIPTS

GOLDEN = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'golden')
CASES = sorted(d for d in os.listdir(GOLDEN) if os.path.isfile(os.path.join(GOLDEN, d, 'meta.json')))


def params():
    for c in CASES:
        meta = json.load(open(os.path.join(GOLDEN, c, 'meta.json')))
        marks = [pytest.mark.lean]
        if meta.get('status') == 'xfail':
            marks.append(pytest.mark.xfail(reason=meta['why'], strict=True))
        yield pytest.param(c, marks=marks, id=c)


@pytest.mark.parametrize('case', params())
def test_rebuild_matches_accepted(case, tmp_path):
    import build_solutions as B
    from prune_solution import _workspace
    meta = json.load(open(os.path.join(GOLDEN, case, 'meta.json')))
    ws = _workspace()
    dst = os.path.join(ws, 'Solutions', 'Golden', case)
    assert dst.startswith(os.path.join(ws, 'Solutions', 'Golden') + os.sep)
    if os.path.isdir(dst):
        shutil.rmtree(dst)
    shutil.copytree(os.path.join(GOLDEN, case, 'src'), dst)
    try:
        name, st, _ = B.build(str(tmp_path), ['Golden/%s/%s' % (case, meta['check'])], meta['target'], str(tmp_path))
        assert st in ('OK', 'OK*'), st
        f = tmp_path / ('Sol_%s.lean' % meta['target'])
        r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'prune_solution.py'), str(f), '--check'],
                           capture_output=True, text=True, cwd=ws)
        assert r.returncode == 0, r.stdout[-2000:] + r.stderr[-2000:]
        got = f.read_text()
    finally:
        shutil.rmtree(dst)
    if meta['status'] == 'partial':
        from p2mlib.copies import imports_of
        assert sorted(m for m in imports_of(got) if m.startswith('Theorems.')) == sorted(meta['theorem_imports'])
        return
    want_path = os.path.join(GOLDEN, case, 'expected.lean')
    want = open(want_path).read()
    dropped = meta.get('dropped_since_accepted', {})
    if dropped:
        from p2mlib import leaninfo, leanedit
        winfo = leaninfo.run(want_path, parse_only=True)
        idx = [leanedit.command_of(winfo, n) for n in dropped]
        assert None not in idx, 'a dropped_since_accepted name is not in expected.lean: %s' % dropped
        want = leanedit.remove_commands(winfo, idx)
    for m in meta.get('imports_dropped_since_accepted', {}):
        assert re.search(r'(?m)^import %s$' % re.escape(m), want), 'not imported by expected.lean: ' + m
        want = re.sub(r'(?m)^import %s\n' % re.escape(m), '', want)

    def norm(t):
        lines = [line for line in t.splitlines(True) if line.strip()]
        # the lines that only give `theorem solution` its scope (`section`, its `open`s, `end`) are
        # the builder's choice: since Phase 4.3 one section with the scope's opens, before it a
        # stack of `open ... in`; that they suffice is what the compile check above proves
        k = max(i for i, l in enumerate(lines) if l.startswith('theorem solution'))
        j = k
        while j and re.match(r'(section|open\s.*)\n?$', lines[j - 1]):
            j -= 1
        while lines[-1].strip() == 'end':
            lines.pop()
        lines = lines[:j] + lines[k:]
        return ''.join(sorted(l for l in lines if l.startswith('import ')) +
                       [l for l in lines if not l.startswith('import ')])
    got, want = norm(got), norm(want)
    if got != want:
        diff = ''.join(list(difflib.unified_diff(want.splitlines(True), got.splitlines(True), 'accepted', 'rebuilt', n=1))[:80])
        pytest.fail('rebuilt solution differs from the accepted one:\n' + diff)
