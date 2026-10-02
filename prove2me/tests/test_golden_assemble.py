"""assemble_blueprint.py on real Blueprint jobs (golden_assemble/<case>/: src/Blueprint.lean,
src/Part*.lean, meta.json, and expected.lean when the output is pinned).

* pinned cases: the assembled text must equal expected.lean;
* every case: the assembled file compiles, no declaration of it uses `sorry`, and its top theorem
  uses only the axioms in meta.json -- plus `sorryAx` when it imports the published theorems
  listed under `published`, which are `sorry` stubs in the workspace.
The assembler elaborates its input (LeanInfo), so both need P2M_LEAN=1. A case marked xfail is a
known assembler bug; the xfail is strict."""
import glob
import json
import os
import shutil
import subprocess
import sys

import pytest

from conftest import SCRIPTS

G = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'golden_assemble')
CASES = sorted(os.listdir(G))


def assemble(case, out):
    src = os.path.join(G, case, 'src')
    parts = sorted(glob.glob(os.path.join(src, 'Part*.lean')))
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'assemble_blueprint.py'),
                        os.path.join(src, 'Blueprint.lean'), str(out)] + parts, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    return out.read_text()


@pytest.mark.lean
@pytest.mark.parametrize('case', [c for c in CASES if os.path.exists(os.path.join(G, c, 'expected.lean'))])
def test_assembly_matches_pinned(case, tmp_path):
    assert assemble(case, tmp_path / 'out.lean') == open(os.path.join(G, case, 'expected.lean')).read()


def compile_params():
    for c in CASES:
        meta = json.load(open(os.path.join(G, c, 'meta.json')))
        marks = [pytest.mark.lean]
        if meta['status'] == 'xfail':
            marks.append(pytest.mark.xfail(reason=meta['why'], strict=True))
        yield pytest.param(c, marks=marks, id=c)


@pytest.mark.parametrize('case', compile_params())
def test_assembled_compiles_with_expected_axioms(case, tmp_path):
    from prune_solution import _workspace
    meta = json.load(open(os.path.join(G, case, 'meta.json')))
    ws = _workspace()
    d = os.path.join(ws, 'Solutions', 'GoldenAsm')
    os.makedirs(d, exist_ok=True)
    f = os.path.join(d, case + '.lean')
    try:
        text = assemble(case, tmp_path / 'out.lean') + '\n#print axioms %s\n' % meta['top']
        open(f, 'w').write(text)
        r = subprocess.run(['lake', 'env', 'lean', f], capture_output=True, text=True, cwd=ws, timeout=3000)
    finally:
        shutil.rmtree(d)
    out = r.stdout + r.stderr
    assert 'error' not in out, out[:3000]
    assert "declaration uses 'sorry'" not in out
    ax = {a.strip() for a in out.split('depends on axioms: [', 1)[1].split(']', 1)[0].replace('\n', ' ').split(',')}
    if 'sorryAx' in ax:
        # only through the imported published statements (sorry stubs in the workspace)
        assert meta.get('published'), ax
        for full in meta['published']:
            assert 'import Theorems.Thm_%s\n' % full.replace('.', '_') in text, full
        ax.discard('sorryAx')
    assert ax <= set(meta['axioms']), ax
