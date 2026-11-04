"""assemble_blueprint.py: a Blueprint's `import Solutions.*` helper modules are inlined, never kept; a
Part another Part imports is assembled once; copy-header Parts (q159) lose their verified copies."""
import json
import os
import shutil
import subprocess
import sys

import pytest

import assemble_blueprint as AB
from conftest import SCRIPTS
from p2mlib import leaninfo

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures', 'assemble')


def fixture(name):
    """The recorded parse-only LeanInfo of lean_fixtures/assemble/<name>.lean (record_fixtures.py assemble)."""
    text = open(os.path.join(FIX, name + '.lean'), 'rb').read()
    return leaninfo.parse(json.load(open(os.path.join(FIX, name + '.parse.json'), encoding='utf-8')), text)


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


# --- a Part imported by another Part (q155, Viterbo 2-product formula, 2026-11-03) ---

def test_a_part_another_part_imports_is_found_among_the_helpers(tmp_path):
    # Part G replaced its stub by `import Solutions.Viterbo.PP2PartL`; Part L was inlined through that
    # import AND assembled as a Part: "`...PartL.pI_comm` has already been declared"
    ws = str(tmp_path)
    l = write(os.path.join(ws, 'Solutions', 'X', 'PartL.lean'), 'import Mathlib\n\ndef l := 1\n')
    copy = write(os.path.join(ws, 'elsewhere', 'PartU.lean'), 'import Mathlib\n\ndef u := 1\n')
    write(os.path.join(ws, 'Solutions', 'X', 'PartU.lean'), 'import Mathlib\n\ndef u := 1\n')
    write(os.path.join(ws, 'Solutions', 'X', 'Tools.lean'), 'import Mathlib\n')
    helpers = [('Solutions.X.Tools', os.path.join(ws, 'Solutions', 'X', 'Tools.lean')),
               ('Solutions.X.PartL', l), ('Solutions.X.PartU', os.path.join(ws, 'Solutions', 'X', 'PartU.lean'))]
    g = write(os.path.join(ws, 'Solutions', 'X', 'PartG.lean'), 'import Solutions.X.PartL\n')
    # by path, or (a copy outside the workspace) by identical text
    assert AB.imported_parts(helpers, [l, g, copy]) == {'Solutions.X.PartL': 0, 'Solutions.X.PartU': 2}


def test_parts_are_ordered_so_an_imported_part_comes_first():
    texts = ['import Solutions.X.PartL\nimport Mathlib\n', 'import Mathlib\n', 'import Mathlib\n',
             'import Solutions.X.PartG\n']
    imported = {'Solutions.X.PartL': 1, 'Solutions.X.PartG': 0}
    # G imports L, H imports G; U keeps its place among the rest
    assert AB.order_parts(texts, imported) == [1, 0, 2, 3]
    assert AB.order_parts(['import Mathlib\n'] * 3, {}) == [0, 1, 2]


def test_parts_importing_each_other_are_refused():
    texts = ['import Solutions.X.PartL\n', 'import Solutions.X.PartG\n']
    with pytest.raises(SystemExit) as e:
        AB.order_parts(texts, {'Solutions.X.PartL': 1, 'Solutions.X.PartG': 0})
    assert 'cycle' in str(e.value)


def test_a_helper_importing_a_part_is_refused(tmp_path):
    # the helper is inlined ahead of the Blueprint, the Part after it: no order works
    ws = str(tmp_path)
    l = write(os.path.join(ws, 'Solutions', 'X', 'PartL.lean'), 'import Mathlib\n')
    t = write(os.path.join(ws, 'Solutions', 'X', 'Tools.lean'), 'import Solutions.X.PartL\n')
    with pytest.raises(SystemExit) as e:
        AB.check_helpers_import_no_part([('Solutions.X.PartL', l), ('Solutions.X.Tools', t)],
                                        {'Solutions.X.PartL': 0})
    assert 'Solutions.X.Tools' in str(e.value) and 'Solutions.X.PartL' in str(e.value)


# --- copy-header Parts (q159, Tao §4: parab, pbr, Thm 4.10 K2N; 2026-11-03) ---

def test_copied_header_is_dropped_and_the_part_keeps_its_own_text():
    bp = fixture('Blueprint')
    text, copied, assumed = AB.drop_copies(fixture('PartB'), bp, 'PartB')
    assert copied == ['BP.two'] and assumed == ['BP.two_eq']
    assert 'def two' not in text and 'sorry' not in text and 'ASSUMED' not in text
    assert 'namespace BP.PartB\n\ntheorem four_eq : BP.two + BP.two = 4 := by rw [BP.two_eq]' in text
    # the scope commands stay: what the Part's own declarations see is unchanged
    assert text.count('namespace BP\n') == 1 and 'end BP\n' in text


def test_print_commands_and_copied_module_docs_go_too():
    text, copied, assumed = AB.drop_copies(fixture('PartA'), fixture('Blueprint'), 'PartA')
    assert copied == ['BP.two'] and assumed == []
    assert '#print' not in text and 'theorem two_eq : BP.two = 2 := rfl' in text
    # the Part's own module doc is not Blueprint text: kept
    assert '# Part A' in text


def test_a_part_without_copies_is_returned_unchanged():
    # Viterbo Part U imports only Mathlib and Definitions and declares only its own names: an
    # ordinary Part, kept whole (its `#print` too, as for an importing Part)
    info = fixture('PartU')
    assert AB.drop_copies(info, fixture('Blueprint'), 'PartU') == (info.text_bytes.decode(), [], [])


@pytest.mark.parametrize('part, why', [
    ('PartBadDef', 'BP.two'),          # a copied definition that is not the Blueprint's
    ('PartBadStub', 'BP.two_eq'),      # an assumed stub stated differently
    ('PartBadAssume', 'BP.two_pos'),   # a `sorry` assumption the Blueprint does not make
    ('PartBadProof', 'BP.two_eq'),     # a stub proved under the Blueprint's own name
])
def test_a_copy_that_is_not_blueprint_text_is_refused(part, why):
    with pytest.raises(SystemExit) as e:
        AB.drop_copies(fixture(part), fixture('Blueprint'), part)
    assert part in str(e.value) and why in str(e.value)


def test_target_is_renamed_dev_and_solution_states_it_at_the_root():
    info = fixture('Blueprint')
    i = next(c.index for c in info.commands if 'BP.top' in c.names)
    assert AB.renamed(info, i).startswith('theorem top_dev (n : Nat) (h : n = 0) : two + two + n = 4 := by')
    assert AB.solution_text(info, i, 'BP.top') == (
        'section\nopen BP\n'
        'theorem solution (n : Nat) (h : n = 0) : two + two + n = 4 := by\n  exact BP.top_dev n h\nend\n')


def run_assemble(*args):
    return subprocess.run([sys.executable, os.path.join(SCRIPTS, 'assemble_blueprint.py')] + [str(a) for a in args],
                          capture_output=True, text=True)


def compile_ok(path, ws):
    r = subprocess.run(['lake', 'env', 'lean', str(path)], capture_output=True, text=True, cwd=ws, timeout=600)
    out = r.stdout + r.stderr
    assert 'error' not in out and 'sorryAx' not in out and "declaration uses 'sorry'" not in out, out
    return out


@pytest.mark.lean
def test_copy_header_parts_assemble_into_a_solution(tmp_path):
    # q159 (Tao §4): Parts import only Mathlib + Definitions and copy the Blueprint's definitions and the
    # stubs they assume; the Blueprint is never a module. Part B (listed first) assumes Part A's stub.
    from prune_solution import _workspace
    hdr = 'import Batteries.Tactic.Alias\n\n'
    files = {}
    for n in ('Blueprint', 'PartB', 'PartA'):
        files[n] = write(str(tmp_path / 'src' / (n + '.lean')), hdr + open(os.path.join(FIX, n + '.lean')).read())
    out = tmp_path / 'out.lean'
    r = run_assemble(files['Blueprint'], out, files['PartB'], files['PartA'], '--target', 'BP.top')
    assert r.returncode == 0, r.stdout + r.stderr
    assert 'PartB: dropped its copy of BP.two; assumes BP.two_eq' in r.stdout
    text = out.read_text()
    assert text.count('def two') == 1 and '#print' not in text and 'sorry' not in text
    assert 'theorem top_dev' in text and not any(l.startswith('theorem top ') for l in text.split('\n'))
    # the stub Part B assumes is Part A's, aliased before Part B uses it
    assert text.index('theorem two_eq : BP.two = 2 := rfl') < text.index('alias two_eq := BP.PartA.two_eq') \
        < text.index('theorem four_eq : BP.two + BP.two = 4')
    assert text.rstrip().endswith('exact BP.top_dev n h\nend')
    out.write_text(text + '\n#print axioms solution\n')
    compile_ok(out, _workspace())


@pytest.mark.lean
def test_a_copy_header_part_with_a_wrong_copy_is_refused(tmp_path):
    files = {n: write(str(tmp_path / (n + '.lean')), open(os.path.join(FIX, n + '.lean')).read())
             for n in ('Blueprint', 'PartBadStub')}
    r = run_assemble(files['Blueprint'], tmp_path / 'out.lean', files['PartBadStub'])
    assert r.returncode != 0 and 'PartBadStub' in r.stderr and 'BP.two_eq' in r.stderr
    assert not (tmp_path / 'out.lean').exists()


@pytest.mark.lean
def test_a_part_imported_by_another_part_is_assembled_once(tmp_path):
    # q155 (Viterbo 2-product formula): Part G imports Part L for its target; listing both gave
    # "`...PartL.a_eq` has already been declared"
    from prune_solution import _workspace
    ws = _workspace()
    d = os.path.join(ws, 'Solutions', 'AsmPartImportTest')
    try:
        bp = write(os.path.join(d, 'Blueprint.lean'),
                   'import Batteries.Tactic.Alias\n\nnamespace API\n\ndef one : Nat := 1\n\n'
                   'theorem a_eq : one = 1 := by\n  sorry\n\ntheorem b_eq : one + one = 2 := by\n  sorry\n\n'
                   'theorem top : one + one + one = 3 := by\n  rw [b_eq, a_eq]\n\nend API\n')
        pl = write(os.path.join(d, 'PartL.lean'),
                   'import Solutions.AsmPartImportTest.Blueprint\n\nnamespace API.PartL\n\n'
                   'theorem a_eq : API.one = 1 := rfl\n\nend API.PartL\n')
        pg = write(os.path.join(d, 'PartG.lean'),
                   'import Solutions.AsmPartImportTest.Blueprint\nimport Solutions.AsmPartImportTest.PartL\n\n'
                   'namespace API.PartG\n\ntheorem b_eq : API.one + API.one = 2 := by\n'
                   '  rw [API.PartL.a_eq]\n\nend API.PartG\n')
        out = tmp_path / 'out.lean'
        r = run_assemble(bp, out, pg, pl)
        assert r.returncode == 0, r.stdout + r.stderr
        assert 'PartL' in r.stdout and 'imported by PartG' in r.stdout
        assert '(2 stubs replaced)' in r.stdout
        text = out.read_text()
        assert text.count('theorem a_eq : API.one = 1 := rfl') == 1 and 'import Solutions.' not in text
        out.write_text(text + '\n#print axioms API.top\n')
        compile_ok(out, ws)
    finally:
        shutil.rmtree(d, ignore_errors=True)
