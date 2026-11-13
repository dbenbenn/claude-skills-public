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


def test_a_helper_importing_the_blueprint_or_a_part_is_promoted_to_a_part(tmp_path):
    # q188 (S9 Pisier): such a helper uses Blueprint text, and inlined ahead of the Blueprint it failed
    # ("unknown identifier tOp"); it is assembled as a Part instead, as is a helper importing one
    ws = str(tmp_path)
    l = write(os.path.join(ws, 'Solutions', 'X', 'PartL.lean'), 'import Mathlib\n')
    t = write(os.path.join(ws, 'Solutions', 'X', 'Tools.lean'), 'import Solutions.X.PartL\n')
    d = write(os.path.join(ws, 'Solutions', 'X', 'Defs.lean'), 'import Solutions.X.Blueprint\n')
    e = write(os.path.join(ws, 'Solutions', 'X', 'More.lean'), 'import Solutions.X.Defs\n')
    f = write(os.path.join(ws, 'Solutions', 'X', 'Base.lean'), 'import Mathlib\n')
    helpers = [('Solutions.X.Base', f), ('Solutions.X.PartL', l), ('Solutions.X.Tools', t),
               ('Solutions.X.Defs', d), ('Solutions.X.More', e)]
    assert AB.promote_helpers(helpers, {'Solutions.X.Blueprint'}, {'Solutions.X.PartL': 0}) == \
        ['Solutions.X.Tools', 'Solutions.X.Defs', 'Solutions.X.More']


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
    ('PartBadSameName', 'BP.two_eq'),  # a stub proved under the Blueprint's own name, restated
])
def test_a_copy_that_is_not_blueprint_text_is_refused(part, why):
    with pytest.raises(SystemExit) as e:
        AB.drop_copies(fixture(part), fixture('Blueprint'), part)
    assert part in str(e.value) and why in str(e.value)


def test_a_stub_proved_under_the_blueprint_name_moves_to_the_parts_namespace():
    # q195: proved under its own name with the stub's statement, it is renamed into the Part's
    # namespace, so the stub becomes its alias as for any Part
    text, copied, assumed = AB.drop_copies(fixture('PartSameName'), fixture('Blueprint'), 'PartSameName')
    assert copied == ['BP.two'] and assumed == []
    assert 'theorem PartSameName.two_eq : two = 2 := rfl' in text and 'def two' not in text


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


# --- 2026-11-05 lessons: q165, q167, q181, q182, q187, q188, q195 ---

HDR = 'import Batteries.Tactic.Alias\n\n'
BP_API = (HDR + 'namespace API\n\ndef one : Nat := 1\n\ntheorem a_eq : one = 1 := by\n  sorry\n\n'
          'theorem b_eq : one + one = 2 := by\n  sorry\n\ntheorem top : one + one + one = 3 := by\n'
          '  rw [b_eq, a_eq]\n\nend API\n')


class Case:
    """Lean files of one assembly case under $P2M_WORKSPACE/Solutions/<name> (removed afterwards)."""

    def __init__(self, name):
        from prune_solution import _workspace
        self.ws = _workspace()
        self.mod = 'Solutions.' + name
        self.dir = os.path.join(self.ws, 'Solutions', name)
        shutil.rmtree(self.dir, ignore_errors=True)

    def file(self, stem, text):
        return write(os.path.join(self.dir, stem + '.lean'), text.replace('$M', self.mod))

    def __enter__(self):
        return self

    def __exit__(self, *a):
        shutil.rmtree(self.dir, ignore_errors=True)


def assembled_ok(r, out, ws, top):
    """The assembly succeeded and OUT compiles without `sorry`; OUT's text."""
    assert r.returncode == 0, r.stdout + r.stderr
    text = out.read_text()
    out.write_text(text + '\n#print axioms %s\n' % top)
    compile_ok(out, ws)
    return text


@pytest.mark.lean
def test_a_hoisted_universe_is_not_redeclared_per_chunk(tmp_path):
    # q167 (Viterbo capacity): an inlined helper's `universe u3 u4` was hoisted to the top AND
    # re-created in every chunk ("a universe level named u3 has already been declared", ~40 errors),
    # and the script still exited 0
    with Case('AsmUniverseTest') as c:
        c.file('Tools', HDR + 'universe u\n\nsection\nabbrev Same (α : Sort u) : Sort u := α\nend\n')
        bp = c.file('Blueprint', HDR + 'import $M.Tools\n\nnamespace AU\n\ndef one : Same Nat := (1 : Nat)\n\n'
                    'theorem a_eq : (one : Nat) = 1 := by\n  sorry\n\ntheorem top : (one : Nat) + 0 = 1 := by\n'
                    '  rw [Nat.add_zero, a_eq]\n\nend AU\n')
        pa = c.file('PartA', HDR + 'import $M.Blueprint\n\nnamespace AU.PartA\n\n'
                    'theorem a_eq : (AU.one : Nat) = 1 := rfl\n\nend AU.PartA\n')
        out = tmp_path / 'out.lean'
        text = assembled_ok(run_assemble(bp, out, pa), out, c.ws, 'AU.top')
        assert text.count('universe u') == 1


@pytest.mark.lean
def test_print_commands_are_stripped_from_parts_and_blueprint(tmp_path):
    # q188: a stray `#print axioms` in PartB was carried into the chunks ("Unknown constant
    # PartB.rescale"); the Blueprint's `#print axioms API.top` names a theorem --target renames
    with Case('AsmPrintTest') as c:
        bp = c.file('Blueprint', BP_API + '\n#print axioms API.top\n')
        pa = c.file('PartA', HDR + 'import $M.Blueprint\n\nnamespace API.PartA\n\n#check API.one\n\n'
                    'theorem a_eq : API.one = 1 := rfl\n\n#print axioms a_eq\n\nend API.PartA\n\n'
                    '#print axioms API.PartA.a_eq\n')
        pb = c.file('PartB', HDR + 'import $M.Blueprint\n\nnamespace API.PartB\n\n#eval API.one\n\n'
                    'theorem b_eq : API.one + API.one = 2 := rfl\n\nend API.PartB\n')
        out = tmp_path / 'out.lean'
        text = assembled_ok(run_assemble(bp, out, pa, pb, '--target', 'API.top'), out, c.ws, 'solution')
        assert '#print' not in text and '#check' not in text and '#eval' not in text


@pytest.mark.lean
def test_a_helper_importing_the_blueprint_is_assembled_after_it(tmp_path):
    # q188 (S9 Pisier): helper modules importing the Blueprint, not listed as Parts, were inlined
    # ahead of the Blueprint text they use ("unknown identifier tOp")
    with Case('AsmHelperBPTest') as c:
        bp = c.file('Blueprint', BP_API)
        c.file('Defs', HDR + 'import $M.Blueprint\n\nnamespace API.PartD\n\ndef two : Nat := API.one + API.one\n\n'
               'theorem two_eq : two = 2 := rfl\n\nend API.PartD\n')
        pa = c.file('PartA', HDR + 'import $M.Blueprint\n\nnamespace API.PartA\n\n'
                    'theorem a_eq : API.one = 1 := rfl\n\nend API.PartA\n')
        pb = c.file('PartB', HDR + 'import $M.Blueprint\nimport $M.Defs\n\nnamespace API.PartB\n\n'
                    'theorem b_eq : API.one + API.one = 2 := API.PartD.two_eq\n\nend API.PartB\n')
        out = tmp_path / 'out.lean'
        text = assembled_ok(run_assemble(bp, out, pa, pb), out, c.ws, 'API.top')
        assert text.index('def one') < text.index('def two') < text.index('alias b_eq')


PART_G = (HDR + 'import $M.Blueprint\n\nnamespace API.PartG\n\n'
          'theorem b_eq : API.one + API.one = 2 := by\n  rw [API.a_eq]\n\ndef g : Nat := 1\n\nend API.PartG\n')


@pytest.mark.lean
def test_a_part_opening_another_parts_namespace_comes_after_it(tmp_path):
    # q181 (strong convergence, cited graphs): PartT's chunk header `open Finset ...PartG` was placed
    # before PartG's chunks ("unknown namespace"), so `Finset` was not opened either
    with Case('AsmOpenTest') as c:
        bp = c.file('Blueprint', BP_API)
        pg = c.file('PartG', HDR + 'import $M.Blueprint\n\nnamespace API.PartG\n\n'
                    'theorem b_eq : API.one + API.one = 2 := rfl\n\ndef g : Nat := 1\n\nend API.PartG\n')
        pt = c.file('PartT', HDR + 'import $M.Blueprint\nimport $M.PartG\n\nopen Nat API.PartG\n\n'
                    'namespace API.PartT\n\ndef t : Nat := succ 0\n\n'
                    'theorem a_eq : API.one = 1 := by\n  have : g = t := rfl\n  rfl\n\nend API.PartT\n')
        out = tmp_path / 'out.lean'
        text = assembled_ok(run_assemble(bp, out, pt, pg), out, c.ws, 'API.top')
        assert text.index('theorem b_eq') < text.index('def t')


@pytest.mark.lean
def test_an_open_no_order_can_satisfy_is_dropped_when_unused(tmp_path):
    # q181, the other way round: PartG's first declaration uses the stub PartT proves, so PartT's
    # chunks must come first; they do not use PartG, so its namespace leaves their `open`
    with Case('AsmOpenCycle2Test') as c:
        bp = c.file('Blueprint', BP_API)
        pg = c.file('PartG', PART_G)
        pt = c.file('PartT', HDR + 'import $M.Blueprint\nimport $M.PartG\n\nopen Nat API.PartG\n\n'
                    'namespace API.PartT\n\ndef t : Nat := succ 0\n\n'
                    'theorem a_eq : API.one = 1 := rfl\n\nend API.PartT\n')
        out = tmp_path / 'out.lean'
        r = run_assemble(bp, out, pt, pg)
        text = assembled_ok(r, out, c.ws, 'API.top')
        assert 'API.PartG' in r.stderr          # the note that it left PartT's `open`
        assert text.index('def t') < text.index('theorem b_eq')


@pytest.mark.lean
def test_a_scope_a_part_leaves_open_is_closed(tmp_path):
    # q182 (strong convergence, high degree): PartQM ended `end PartQM` but left `namespace
    # StrongConv.HighDegUp` open; concatenated, "Missing name after `end`"
    with Case('AsmScopeTest') as c:
        bp = c.file('Blueprint', BP_API)
        pa = c.file('PartA', HDR + 'import $M.Blueprint\n\nnamespace API\nnamespace PartA\n\n'
                    'theorem a_eq : API.one = 1 := rfl\n\nend PartA\n')
        pb = c.file('PartB', HDR + 'import $M.Blueprint\n\nnamespace API.PartB\n\n'
                    'theorem b_eq : API.one + API.one = 2 := rfl\n\nend API.PartB\n')
        out = tmp_path / 'out.lean'
        r = run_assemble(bp, out, pa, pb)
        assembled_ok(r, out, c.ws, 'API.top')
        assert 'PartA' in r.stderr and 'end API' in r.stderr


@pytest.mark.lean
def test_a_partial_blueprint_proof_restated_by_a_part_is_a_stub(tmp_path):
    # q187 (high degree retry): the Blueprint's main theorem was started and ended in `sorry`; PartM
    # restated and proved it, but only whole-body `sorry` stubs were replaced, and nothing warned
    with Case('AsmPartialTest') as c:
        bp = c.file('Blueprint', HDR + 'namespace API\n\ndef one : Nat := 1\n\ntheorem a_eq : one = 1 := by\n'
                    '  sorry\n\ntheorem top : one + one = 2 := by\n  have h := a_eq\n  sorry\n\nend API\n')
        pa = c.file('PartA', HDR + 'import $M.Blueprint\n\nnamespace API.PartA\n\n'
                    'theorem a_eq : API.one = 1 := rfl\n\nend API.PartA\n')
        pm = c.file('PartM', HDR + 'import $M.Blueprint\n\nnamespace API.PartM\n\n'
                    'theorem top : API.one + API.one = 2 := by\n  rw [API.a_eq]\n\nend API.PartM\n')
        out = tmp_path / 'out.lean'
        r = run_assemble(bp, out, pa)          # without PartM: top keeps its `sorry`
        assert r.returncode != 0 and 'API.top' in r.stderr and 'sorry' in r.stderr
        r = run_assemble(bp, out, pa, '--allow-sorry')
        assert r.returncode == 0 and 'API.top' in r.stderr
        r = run_assemble(bp, out, pa, pm)
        text = assembled_ok(r, out, c.ws, 'API.top')
        assert 'alias top := API.PartM.top' in text and 'sorry' not in text
        r = run_assemble(bp, out, pa, pm, '--target', 'API.top')
        assembled_ok(r, out, c.ws, 'solution')


@pytest.mark.lean
def test_target_proved_in_a_blueprint_sub_namespace(tmp_path):
    # q165 (Tao decay leaf): the Blueprint proved TaoBR.TaoDecay.X for the published TaoBR.X, and
    # --target TaoBR.X refused
    with Case('AsmTargetNsTest') as c:
        bp = c.file('Blueprint', BP_API.replace('namespace API\n', 'namespace API.Sub\n')
                    .replace('end API\n', 'end API.Sub\n'))
        pa = c.file('PartA', HDR + 'import $M.Blueprint\n\nnamespace API.Sub.PartA\n\n'
                    'theorem a_eq : API.Sub.one = 1 := rfl\n\nend API.Sub.PartA\n')
        pb = c.file('PartB', HDR + 'import $M.Blueprint\n\nnamespace API.Sub.PartB\n\n'
                    'theorem b_eq : API.Sub.one + API.Sub.one = 2 := rfl\n\nend API.Sub.PartB\n')
        out = tmp_path / 'out.lean'
        text = assembled_ok(run_assemble(bp, out, pa, pb, '--target', 'API.top'), out, c.ws, 'solution')
        assert 'top_dev' not in text and 'exact API.Sub.top' in text


@pytest.mark.lean
def test_copy_header_parts_proving_under_the_blueprint_name_assemble(tmp_path):
    # q195 (Guth-Maynard Cor 1.3): Parts proved each stub under the Blueprint's own name, with
    # sorried copies of the sibling stubs they used; the assembler refused and the worker hand-merged
    from prune_solution import _workspace
    files = {n: write(str(tmp_path / 'src' / (n + '.lean')), HDR + open(os.path.join(FIX, n + '.lean')).read())
             for n in ('Blueprint', 'PartB', 'PartSameName')}
    out = tmp_path / 'out.lean'
    r = run_assemble(files['Blueprint'], out, files['PartB'], files['PartSameName'], '--target', 'BP.top')
    text = assembled_ok(r, out, _workspace(), 'solution')
    assert 'alias two_eq := BP.PartSameName.two_eq' in text


@pytest.mark.lean
def test_a_helper_sharing_a_stubs_name_with_another_statement_is_not_its_proof(tmp_path):
    # q200 (Guth-Maynard Prop 9.1): PartG kept a helper `card_dyadic_le` (`0 < M`, bound `3M`) beside the
    # stub of that name (`0 ≤ M`, bound `M + 1`) that PartB proved; the stub was aliased to PartG's helper
    # (the last Part listed won) and every use of the stub failed to elaborate
    with Case('AsmHelperNameTest') as c:
        bp = c.file('Blueprint', BP_API)
        pa = c.file('PartA', HDR + 'import $M.Blueprint\n\nnamespace API.PartA\n\n'
                    'theorem a_eq : API.one = 1 := rfl\n\nend API.PartA\n')
        pb = c.file('PartB', HDR + 'import $M.Blueprint\n\nnamespace API.PartB\n\n'
                    'theorem a_eq : API.one * 1 = 1 := rfl\n\n'
                    'theorem b_eq : API.one + API.one = 2 := rfl\n\nend API.PartB\n')
        out = tmp_path / 'out.lean'
        text = assembled_ok(run_assemble(bp, out, pa, pb, '--target', 'API.top'), out, c.ws, 'solution')
        assert 'alias a_eq := API.PartA.a_eq' in text


# --- a Blueprint stub replaced by a published statement (q196, q200, q209), a `_dev` target (q208) ---

def _assemble(tmp_path, bp_text, part_text, *extra):
    from prune_solution import _workspace
    ws = _workspace()
    d = os.path.join(ws, 'Solutions', 'AsmPubTest')
    try:
        bp = write(os.path.join(d, 'Blueprint.lean'), bp_text)
        part = write(os.path.join(d, 'PartA.lean'), part_text)
        out = tmp_path / 'out.lean'
        r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'assemble_blueprint.py'), bp, str(out), part,
                            *extra], capture_output=True, text=True)
        return r, (out.read_text() if out.exists() else '')
    finally:
        shutil.rmtree(d, ignore_errors=True)


PUB_BP = '''import Mathlib

namespace APT

noncomputable def inv (n : ℕ) : ℝ := 1 / (n : ℝ)

theorem two_eq : (2 : ℕ) = 1 + 1 := by
  sorry

theorem key {a m : ℕ} (h0 : 0 < m) (hma : m < a) : inv (min m (a - m)) ≤ inv m + inv (a - m) := by
  sorry

theorem top_dev {a m : ℕ} (h0 : 0 < m) (hma : m < a) : inv (min m (a - m)) ≤ inv m + inv (a - m) ∧ 2 = 1 + 1 :=
  ⟨key h0 hma, two_eq⟩

end APT
'''

PUB_PART = 'import Solutions.AsmPubTest.Blueprint\n\nnamespace APT.PartA\n\ntheorem two_eq : (2 : ℕ) = 1 + 1 := rfl\n\nend APT.PartA\n'


@pytest.mark.lean
def test_published_replaces_a_stub_by_the_published_theorem_and_a_dev_target_is_found(tmp_path):
    # q196/q209: a slow Blueprint proof was cut at stubs published as statements, and every piece wired them
    # in by a job-local script (whose lazy regex once deleted a Part's `end`); the published form may be the
    # stub's with its definitions unfolded. q208: --target NAME refused a Blueprint proving it as NAME_dev
    r, text = _assemble(tmp_path, PUB_BP, PUB_PART, '--target', 'APT.top',
                        '--published', 'APT.key=Theorems.Thm_BlockCycleRotation_one_div_min_le')
    assert r.returncode == 0, r.stdout + r.stderr
    assert 'import Theorems.Thm_BlockCycleRotation_one_div_min_le\n' in text
    assert 'exact BlockCycleRotation.one_div_min_le h0 hma' in text and 'sorry' not in text
    assert 'exact APT.top_dev h0 hma' in text


@pytest.mark.lean
def test_published_refuses_a_name_that_is_no_stub(tmp_path):
    r, _ = _assemble(tmp_path, PUB_BP, PUB_PART, '--published', 'APT.inv=Theorems.Thm_BlockCycleRotation_one_div_min_le')
    assert r.returncode != 0 and 'not a Blueprint stub' in r.stdout + r.stderr


# --- a Blueprint stacked on another Blueprint (q284), a Part outside the Blueprint's namespace (q353) ---

def test_a_helper_with_stubs_that_a_part_restates_is_an_inner_blueprint(tmp_path):
    # q284 (strong convergence, Puder retry): Q284Cnt imported the Blueprint Q284Sch, whose stubs Parts
    # S1-S4 proved; Q284Sch was inlined with its `sorry` stubs kept although S1-S4 were on the command line
    ws = str(tmp_path)
    a = write(os.path.join(ws, 'Solutions', 'X', 'Sch.lean'),
              'import Mathlib\n\nnamespace SA\n\ntheorem a_eq : 1 = 1 := by\n  sorry\n\nend SA\n')
    t = write(os.path.join(ws, 'Solutions', 'X', 'Tools.lean'), 'import Mathlib\n\n-- not sorry\ndef t := 1\n')
    u = write(os.path.join(ws, 'Solutions', 'X', 'Unused.lean'),
              'import Mathlib\n\nnamespace SU\n\ntheorem u : 1 = 1 := sorry\n\nend SU\n')
    v = write(os.path.join(ws, 'Solutions', 'X', 'Via.lean'),
              'import Mathlib\n\nnamespace SV.Deep\n\ntheorem v : 1 = 1 := sorry\n\nend SV.Deep\n')
    p1 = write(os.path.join(ws, 'Solutions', 'X', 'PartA1.lean'),
               'import Solutions.X.Sch\nimport Solutions.X.Tools\n\nnamespace SA.PartA1\n\nend SA.PartA1\n')
    # a Part reaching the stubs through the outer Blueprint, by its namespace alone
    p2 = write(os.path.join(ws, 'Solutions', 'X', 'PartV.lean'),
               'import Solutions.X.Cnt\n\nnamespace SV.Deep.PartV\n\nend SV.Deep.PartV\n')
    helpers = [('Solutions.X.Sch', a), ('Solutions.X.Tools', t), ('Solutions.X.Unused', u), ('Solutions.X.Via', v)]
    # Tools has no stub; Unused has one, but no Part imports it or opens a namespace under it
    assert AB.inner_blueprints(helpers, [p1, p2]) == ['Solutions.X.Sch', 'Solutions.X.Via']
    assert AB.inner_blueprints(helpers, [p1]) == ['Solutions.X.Sch']


def test_another_blueprint_named_blueprint_is_not_the_blueprint(tmp_path):
    # q284: an inner Blueprint whose module ends in `Blueprint` was taken for the main one and dropped
    ws = str(tmp_path / 'ws')
    bp = write(os.path.join(ws, 'Solutions', 'X', 'Blueprint.lean'), 'import Solutions.X.SchBlueprint\n')
    write(os.path.join(ws, 'Solutions', 'X', 'SchBlueprint.lean'), 'import Mathlib\n')
    texts = ['import Solutions.X.Blueprint\nimport Solutions.X.SchBlueprint\n']
    assert AB.blueprint_modules(bp, texts, ws) == {'Solutions.X.Blueprint'}
    # a Blueprint outside the workspace: an imported *Blueprint is taken for it, as before
    out = write(str(tmp_path / 'src' / 'Blueprint.lean'), 'import Mathlib\n')
    assert AB.blueprint_modules(out, texts, ws) == {'Solutions.X.Blueprint', 'Solutions.X.SchBlueprint'}


STACK_A = (HDR + 'namespace SA\n\ndef one : Nat := 1\n\ntheorem a_eq : one = 1 := by\n  sorry\n\n'
           'theorem two : one + one = 2 := by\n  rw [a_eq]\n\nend SA\n')
STACK_B = (HDR + 'import $M.Sch\n\nnamespace SB\n\ntheorem b_eq : SA.one + SA.one + SA.one = 3 := by\n  sorry\n\n'
           'theorem top : SA.one + (SA.one + SA.one + SA.one) = 4 := by\n  rw [b_eq, SA.a_eq]\n\nend SB\n')


@pytest.mark.lean
def test_a_blueprint_stacked_on_another_blueprint_assembles(tmp_path):
    # q284 (strong convergence, Puder retry): Blueprint Cnt imported Blueprint Sch and used its stubs;
    # assembling Cnt with Sch's Parts S1-S4 on the command line kept Sch's stubs ("still uses sorry:
    # Puder.Q284S.tr_mem ...; no Part proves it"), and the worker assembled Sch by hand first
    with Case('AsmStackTest') as c:
        c.file('Sch', STACK_A)
        bp = c.file('Cnt', STACK_B)
        pa = c.file('PartA1', HDR + 'import $M.Sch\n\nnamespace SA.PartA1\n\n'
                    'theorem a_eq : SA.one = 1 := rfl\n\nend SA.PartA1\n')
        # Part B1 uses the inner stub, so Part A1's proof and its alias must come first
        pb = c.file('PartB1', HDR + 'import $M.Cnt\n\nnamespace SB.PartB1\n\n'
                    'theorem b_eq : SA.one + SA.one + SA.one = 3 := by\n  rw [SA.a_eq]\n\nend SB.PartB1\n')
        out = tmp_path / 'out.lean'
        r = run_assemble(bp, out, pb, pa)
        text = assembled_ok(r, out, c.ws, 'SB.top')
        assert '(2 stubs replaced)' in r.stdout and 'sorry' not in text and 'import Solutions.' not in text
        assert 'alias a_eq := SA.PartA1.a_eq' in text and 'alias b_eq := SB.PartB1.b_eq' in text
        assert text.index('def one') < text.index('theorem a_eq : SA.one = 1 := rfl') \
            < text.index('alias a_eq') < text.index('theorem two') < text.index('alias b_eq')
        r = run_assemble(bp, out, pa, pb, '--target', 'SB.top')
        assembled_ok(r, out, c.ws, 'solution')


def test_a_part_restating_a_stub_outside_the_blueprint_namespace_is_refused():
    # q353 (STOC linear max load retry): Parts namespaced `LML.Dev.Part<X>` instead of `LML.Part<X>`
    # matched no stub, and the assembly kept all seven
    part_ns = {('PartA', 'LML.Dev.PartA'): ['LML.Dev.PartA.a_eq', 'LML.Dev.PartA.helper'],
               ('PartB', 'LML.PartB'): ['LML.PartB.b_eq'],
               ('PartH', 'Aux.PartH'): ['Aux.PartH.h']}
    bp_ns = {'LML', 'LML.Sub'}
    refuse, warn = AB.misplaced_parts(part_ns, bp_ns, ['LML.a_eq', 'LML.Sub.c_eq'])
    assert len(refuse) == 1 and 'PartA' in refuse[0] and 'LML.Dev.PartA' in refuse[0]
    assert 'LML.PartA' in refuse[0] and 'LML.a_eq' in refuse[0]
    # a Part-like namespace restating no stub: a loud warning naming the expected namespaces
    assert len(warn) == 1 and 'Aux.PartH' in warn[0] and 'LML.PartH' in warn[0] and 'LML.Sub.PartH' in warn[0]
    assert AB.misplaced_parts({('PartB', 'LML.PartB'): ['LML.PartB.b_eq']}, bp_ns, ['LML.a_eq']) == ([], [])


@pytest.mark.lean
def test_a_part_outside_the_blueprint_namespace_is_refused_by_name(tmp_path):
    # q353: `namespace API.Dev.PartA` restated the stub API.a_eq; the assembly kept it, and the only
    # message said no Part proves it
    with Case('AsmPartNsTest') as c:
        bp = c.file('Blueprint', BP_API)
        pa = c.file('PartA', HDR + 'import $M.Blueprint\n\nnamespace API.Dev.PartA\n\n'
                    'theorem a_eq : API.one = 1 := rfl\n\nend API.Dev.PartA\n')
        pb = c.file('PartB', HDR + 'import $M.Blueprint\n\nnamespace API.PartB\n\n'
                    'theorem b_eq : API.one + API.one = 2 := rfl\n\nend API.PartB\n')
        out = tmp_path / 'out.lean'
        r = run_assemble(bp, out, pa, pb)
        assert r.returncode != 0 and 'API.Dev.PartA' in r.stderr and 'API.PartA' in r.stderr, r.stdout + r.stderr
        assert 'expected API.PartA' in r.stderr and not out.exists()
        # --allow-sorry: assembled with the stub kept, the warning still naming the namespace
        r = run_assemble(bp, out, pa, pb, '--allow-sorry')
        assert r.returncode == 0 and 'expected API.PartA' in r.stderr and 'API.a_eq' in r.stderr
