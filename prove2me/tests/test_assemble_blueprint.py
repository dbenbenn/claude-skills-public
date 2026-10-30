"""assemble_blueprint.py: a Blueprint's `import Solutions.*` helper modules are inlined, never kept."""
import os
import shutil
import subprocess
import sys

import pytest

import assemble_blueprint as AB
from conftest import SCRIPTS


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, 'w', encoding='utf-8').write(text)
    return path


def test_solution_imports_are_the_closure_dependencies_first(tmp_path):
    # oaiq-121 (Tao BR, Carleson-Sjolin leaf): the Blueprint imported Solutions.TaoBRCS.Tools, and the
    # assembled file kept that import, which a submission cannot have
    ws = str(tmp_path)
    write(os.path.join(ws, 'Solutions', 'X', 'Helpers.lean'), 'import Mathlib\nimport Solutions.X.Base\n\ndef h := 1\n')
    write(os.path.join(ws, 'Solutions', 'X', 'Base.lean'), 'import Mathlib\n\ndef b := 0\n')
    write(os.path.join(ws, 'Solutions', 'X', 'More.lean'), '-- import Solutions.X.Nope\nimport Solutions.X.Base\n')
    texts = ['import Mathlib\nimport Solutions.X.Helpers\n',
             'import Solutions.X.Blueprint\nimport Solutions.X.More\nimport Solutions.X.Helpers\n']
    got = AB.solution_imports(texts, {'Solutions.X.Blueprint'}, ws)
    assert [m for m, _ in got] == ['Solutions.X.Base', 'Solutions.X.Helpers', 'Solutions.X.More']
    assert got[0][1] == os.path.join(ws, 'Solutions', 'X', 'Base.lean')


def test_a_solution_import_without_a_file_is_refused(tmp_path):
    with pytest.raises(SystemExit) as e:
        AB.solution_imports(['import Solutions.X.Gone\n'], set(), str(tmp_path))
    assert 'Solutions.X.Gone' in str(e.value) and 'inline' in str(e.value)


def test_header_drops_every_solutions_import():
    texts = ['import Mathlib\nimport Solutions.X.Helpers\nimport Definitions.Def_D\n',
             'import Solutions.X.Blueprint\nimport Theorems.Thm_N_a\nimport Mathlib\n']
    assert AB.header_imports(texts, {'Solutions.X.Blueprint'}) == \
        ['Mathlib', 'Definitions.Def_D', 'Theorems.Thm_N_a']


@pytest.mark.lean
def test_a_blueprint_importing_a_helper_module_assembles_without_solution_imports(tmp_path):
    from prune_solution import _workspace
    ws = _workspace()
    d = os.path.join(ws, 'Solutions', 'AsmHelperTest')
    try:
        # `alias` (the proved stub's replacement) comes from Batteries: the helper's own import must
        # reach the assembled header
        write(os.path.join(d, 'Helpers.lean'),
              'import Batteries.Tactic.Alias\n\nnamespace AHT\n\ndef two : Nat := 2\n\nend AHT\n')
        bp = write(os.path.join(d, 'Blueprint.lean'),
                   'import Solutions.AsmHelperTest.Helpers\n\nnamespace AHT\n\n'
                   'theorem two_eq : two = 2 := by\n  sorry\n\ntheorem top : two + 0 = 2 := by\n'
                   '  simp [two_eq]\n\nend AHT\n')
        part = write(os.path.join(d, 'PartA.lean'),
                     'import Solutions.AsmHelperTest.Blueprint\n\nnamespace AHT.PartA\n\n'
                     'theorem two_eq : AHT.two = 2 := rfl\n\nend AHT.PartA\n')
        out = tmp_path / 'out.lean'
        r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'assemble_blueprint.py'), bp, str(out), part],
                           capture_output=True, text=True)
        assert r.returncode == 0, r.stdout + r.stderr
        text = out.read_text()
        assert 'import Solutions.' not in text and 'def two : Nat := 2' in text
        assert text.startswith('import Batteries.Tactic.Alias\n')
        assert text.index('def two') < text.index('theorem top')
        f = write(os.path.join(d, 'Assembled.lean'), text + '\n#print axioms AHT.top\n')
        r = subprocess.run(['lake', 'env', 'lean', f], capture_output=True, text=True, cwd=ws, timeout=600)
        assert 'error' not in r.stdout + r.stderr and 'sorryAx' not in r.stdout, r.stdout + r.stderr
    finally:
        shutil.rmtree(d, ignore_errors=True)
