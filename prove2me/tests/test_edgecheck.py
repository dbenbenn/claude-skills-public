"""The carve's import-edge check (p2mlib.edgecheck; scripts/carve_measure.py runs it).

Offline: the verdict logic on hand-built EdgeUses output, with compiles faked. The Lean side, on the
CarveDev fixture, is `test_measure_finds_a_false_import_edge` (P2M_LEAN=1)."""
import json
import os
import sys

import pytest

from p2mlib import edgecheck as E

HERE = os.path.dirname(os.path.abspath(__file__))
FIX = os.path.join(HERE, 'lean_fixtures', 'carve')
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'scripts'))


PIECE = ('import Mathlib\nimport Definitions.Def_B0\nimport Theorems.Thm_A\nimport Theorems.Thm_B\n'
         'import Theorems.Thm_C\n\n'
         'theorem dead_lemma : True := Thm_B\n'
         'theorem main_oai : True := Thm_A\n'
         'theorem solution : True := main_oai\n')
# EdgeUses' output for it: `solution` reaches Thm_A and Def_B0; only dead_lemma uses Thm_B
USES = {'live': {'Theorems.Thm_A': ['A'], 'Definitions.Def_B0': ['b']},
        'all': {'Theorems.Thm_A': ['A'], 'Definitions.Def_B0': ['b'], 'Theorems.Thm_B': ['B']}}


def test_candidates_are_theorem_imports_and_for_bundles_this_carves_bundles():
    t = 'import Mathlib\nimport Definitions.Def_X000\nimport Definitions.Def_Pub\nimport Theorems.Thm_T\n'
    assert E.candidates(t, 'piece', ['X000']) == ['Theorems.Thm_T']
    assert E.candidates(t, 'bundle', ['X000']) == ['Definitions.Def_X000', 'Theorems.Thm_T']


def test_a_piece_counts_only_what_solution_reaches():
    v = E.classify(USES, E.candidates(PIECE, 'piece'))
    assert v == {'Theorems.Thm_A': 'used', 'Theorems.Thm_B': 'dead', 'Theorems.Thm_C': 'unused'}


def test_an_unused_import_is_a_false_edge_once_the_file_compiles_without_it():
    seen = []

    def ok(t):
        seen.append(t)
        return True
    r = E.check(PIECE, E.candidates(PIECE, 'piece'), USES, ok, lambda m: [])
    assert r['method'] == 'constants' and r['compiles'] == 1
    assert r['imports'] == {'Theorems.Thm_A': 'used', 'Theorems.Thm_B': 'dead', 'Theorems.Thm_C': 'false'}
    assert r['false'] == ['Theorems.Thm_C']      # dead is reported for pruning, not as a false edge
    assert 'import Theorems.Thm_C' not in seen[0] and 'import Theorems.Thm_A' in seen[0]


def test_a_clean_file_costs_no_compile():
    r = E.check(PIECE, ['Theorems.Thm_A'], USES, lambda t: 1 / 0, lambda m: [])
    assert r['false'] == [] and r['compiles'] == 0
    assert E.check(PIECE, [], None, lambda t: 1 / 0, lambda m: [])['method'] == 'none'


def test_a_bundle_used_only_through_the_false_import_is_imported_instead():
    # the piece uses Def_S only through the stub it falsely imports: drop the stub, import Def_S
    t = 'import Mathlib\nimport Theorems.Thm_C\n\ntheorem solution : True := s_fact\n'
    uses = {'live': {'Definitions.Def_S': ['s_fact']}, 'all': {'Definitions.Def_S': ['s_fact']}}
    seen = []
    r = E.check(t, ['Theorems.Thm_C'], uses, lambda x: seen.append(x) or True,
                lambda m: ['Mathlib', 'Definitions.Def_S'] if m == 'Theorems.Thm_C' else [])
    assert r['false'] == ['Theorems.Thm_C'] and r['restore'] == {'Theorems.Thm_C': ['Definitions.Def_S']}
    assert seen[0].startswith('import Mathlib\nimport Definitions.Def_S\n\ntheorem')


def test_an_import_used_without_a_trace_in_the_terms_is_needed():
    # `dsimp only [h]` with an rfl lemma h, a notation, an `open`: no constant, yet Lean needs it
    r = E.check(PIECE, ['Theorems.Thm_A', 'Theorems.Thm_C'], USES, lambda t: False, lambda m: [])
    assert r['imports']['Theorems.Thm_C'] == 'needed' and r['false'] == []


def test_of_several_unused_imports_each_is_tried_alone_when_together_they_fail():
    uses = {'live': {'Theorems.Thm_A': ['A']}, 'all': {'Theorems.Thm_A': ['A']}}
    r = E.check(PIECE, ['Theorems.Thm_C', 'Definitions.Def_B0'], uses,
                lambda x: 'import Theorems.Thm_C' in x, lambda m: [])
    assert r['imports'] == {'Theorems.Thm_C': 'needed', 'Definitions.Def_B0': 'false'}
    assert r['compiles'] == 3


def test_without_the_scan_each_import_is_recompiled_without_it():
    r = E.check(PIECE, ['Theorems.Thm_A', 'Theorems.Thm_C'], None,
                lambda t: 'import Theorems.Thm_A' in t, lambda m: [])
    assert r['method'] == 'recompile' and r['compiles'] == 2
    assert r['imports'] == {'Theorems.Thm_A': 'needed', 'Theorems.Thm_C': 'false'}


def test_without_keeps_the_rest_of_the_file_byte_for_byte():
    t = 'import A\nimport B\n\n-- import B\ntheorem x : True := trivial\n'
    assert E.without(t, {'B'}) == 'import A\n\n-- import B\ntheorem x : True := trivial\n'
    assert E.without(t, {'B'}, ['C', 'A']) == 'import A\nimport C\n\n-- import B\ntheorem x : True := trivial\n'


# ------------------------------------------------------------- carve_measure's bookkeeping

def test_measure_reports_false_edges_and_orphaned_statements():
    import carve_measure as M
    plan = {'stubs': {'A.t': {}, 'A.u': {}, 'A.forced': {}}, 'targets': ['A.main'],
            'forced': ['A.forced'], 'external': ['A.main'], 'statement_suffix': ''}
    edges = {'piece:A.main': {'file': 'Sol_A_main.lean', 'false': ['Theorems.Thm_A_u'],
                              'imports': {'Theorems.Thm_A_t': 'used', 'Theorems.Thm_A_u': 'false'},
                              'restore': {}},
             'piece:A.t': {'file': 'Sol_A_t.lean', 'false': [], 'imports': {}, 'restore': {}}}
    rep = M.edge_report(plan, edges)
    assert [(f['item'], f['import'], f['statement']) for f in rep['false_edges']] == \
        [('piece:A.main', 'Theorems.Thm_A_u', 'A.u')]
    # A.u is imported by nothing once the false edge goes; A.forced is a named result, kept
    assert rep['orphaned_statements'] == ['A.u']


def test_drop_records_the_cut_so_it_survives_gen(tmp_path):
    import carve_measure as M
    from p2mlib import repair as RP
    src = tmp_path / 'Sol_X.lean'
    src.write_text('import Mathlib\nimport Theorems.Thm_U\n\ntheorem solution : True := trivial\n')
    cuts = M.drop_cuts({'false': ['Theorems.Thm_U'], 'restore': {}})
    assert cuts == ['import Theorems.Thm_U']
    new, applied, stale = RP.apply_cuts(src.read_text(), cuts)
    assert new == 'import Mathlib\ntheorem solution : True := trivial\n' and not stale
    # a false edge that needs a bundle in its place is not a plain cut: left to a person
    assert M.drop_cuts({'false': ['Theorems.Thm_U'], 'restore': {'Theorems.Thm_U': ['Definitions.Def_S']}}) is None


def test_a_false_bundle_import_is_replaced_by_the_bundles_it_brought_in():
    # a bundle importing a bundle it only needs for that bundle's own imports (oaiq-037 K032 -> K018):
    # the cut carries the replacement, applies once and survives a re-apply after gen
    import carve_measure as M
    from p2mlib import repair as RP
    text = 'import Mathlib\nimport Definitions.Def_A\nimport Definitions.Def_B\n\ndef x := 1\n'
    cuts = M.drop_cuts({'false': ['Definitions.Def_B'],
                        'restore': {'Definitions.Def_B': ['Definitions.Def_C', 'Definitions.Def_D']}})
    assert cuts and len(cuts) == 1
    new, applied, stale = RP.apply_cuts(text, cuts)
    assert new == ('import Mathlib\nimport Definitions.Def_A\nimport Definitions.Def_C\n'
                   'import Definitions.Def_D\n\ndef x := 1\n') and applied == cuts and not stale
    assert M.reapply(new, cuts) == (new, [])


def test_recorded_cuts_already_applied_by_gen_are_not_stale():
    # carve.py gen re-applies work/repairs.json now (Boone-Higman, 2026-10-24), so measure finds
    # most recorded cuts already made: silent; a cut whose text is still there but no longer
    # matches as a command is stale
    import carve_measure as M
    text = 'import Mathlib\n\nvariable (a : Nat)\n  (b : Nat)\n\ntheorem t : True := trivial\n'
    cut = ['open Foo', '(b : Nat)']
    new, stale = M.reapply(text, cut)
    assert '(b : Nat)' not in new and stale == []
    assert M.reapply(new, cut) == (new, [])
    assert M.reapply('import Mathlib\nopen Foo Bar\n', ['open Foo'])[1] == ['open Foo']


# ------------------------------------------------------------- with Lean

@pytest.mark.lean
def test_measure_finds_a_false_import_edge(tmp_path):
    # PosteriorReplicas (2026-10-23): a carved piece imported a statement it never used; it compiled,
    # so only a hand check (drop each import, recompile) caught it. carve_measure now checks every
    # `import Theorems.*` against what the file's declarations use, and fails on a false edge.
    import shutil
    import subprocess
    import sys
    work = tmp_path / 'work'
    work.mkdir()
    shutil.copy(os.path.join(FIX, 'decl_graph.jsonl'), work / 'decl_graph.jsonl')
    cfg = tmp_path / 'carve.json'
    cfg.write_text(json.dumps({'src': FIX, 'prefix': 'CarveDev', 'roots': ['CarveDev.Top'],
                               'targets': ['CD.double_succ', 'CD.double_zero', 'CD.main'],
                               'forced': ['CD.double_eq'], 'work': str(work), 'out': str(tmp_path / 'out'),
                               'bundle_prefix': 'CDE', 'budget': 1000, 'bundle_budget': 1000,
                               'bytes_per_second': 10000}))
    scripts = os.path.join(os.path.dirname(HERE), 'scripts')

    def run(script, *a):
        r = subprocess.run([sys.executable, os.path.join(scripts, script)] + list(a), capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr
    assert run('carve.py', 'plan', str(cfg))[0] == 0

    def gen_and_inject():
        assert run('carve.py', 'gen', str(cfg))[0] == 0
        sol = tmp_path / 'out' / 'solutions' / 'Sol_CD_double_succ.lean'
        t = sol.read_text()
        assert 'import Theorems.Thm_CD_double_eq\n' in t      # used: `simp only [double_eq]`
        sol.write_text(t.replace('import Theorems.Thm_CD_double_eq\n',
                                 'import Theorems.Thm_CD_double_eq\nimport Theorems.Thm_CD_double_zero\n'))
        return sol
    sol = gen_and_inject()
    code, out = run('carve_measure.py', str(cfg))
    assert code == 1 and out.rstrip().endswith('FAILED'), out
    assert 'FALSE EDGE piece:CD.double_succ (Sol_CD_double_succ.lean): import Theorems.Thm_CD_double_zero' in out
    rep = json.loads((work / 'false_edges.json').read_text())
    hit = [f for f in rep['false_edges'] if f['item'] == 'piece:CD.double_succ']
    assert [(f['import'], f['statement'], f['verdict']) for f in hit] == \
        [('Theorems.Thm_CD_double_zero', 'CD.double_zero', 'false')]
    edges = json.loads((work / 'edges.json').read_text())
    # the edges a proof does use are kept: a rewrite, a notation (`DE` for double_eq), a statement
    assert edges['piece:CD.double_succ']['method'] == 'constants'      # read from the .olean
    assert edges['piece:CD.double_succ']['compiles'] == 1               # one confirming compile
    assert edges['piece:CD.double_succ']['imports']['Theorems.Thm_CD_double_eq'] == 'used'
    assert edges['piece:CD.double_zero']['imports'] == {'Theorems.Thm_CD_double_eq': 'used'}
    assert edges['piece:CD.main']['imports']['Theorems.Thm_CD_double_succ'] == 'used'
    # skipped on request
    code, out = run('carve_measure.py', str(cfg), '--no-edge-check')
    assert code == 0 and 'FALSE EDGE' not in out, out
    # dropped on request: cut, recorded, re-measured; the cut survives a fresh `carve.py gen`
    code, out = run('carve_measure.py', str(cfg), '--drop-false-edges')
    assert code == 0 and 'edge check: no false edges' in out, out
    assert 'Thm_CD_double_zero' not in sol.read_text()
    assert 'import Theorems.Thm_CD_double_zero' in json.loads((work / 'repairs.json').read_text())['Sol_CD_double_succ.lean']
    gen_and_inject()
    code, out = run('carve_measure.py', str(cfg))
    assert code == 0 and 'Thm_CD_double_zero' not in sol.read_text(), out
