"""The module route of porting an openai/math result (oai_port_modules, oai_build_modules,
carve_prep, carve_measure): each behaviour here differed between the per-carve copies these scripts
replace (2026-10-18). Small fixtures, no Lean, no network, no workspace writes."""
import json
import os

import pytest

import carve_prep as CP
import oai_build_modules as BM
import oai_port_modules as PM
from p2mlib import oaiport as O

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'oaiport_fixtures')
LEAN = os.path.join(FIX, 'lean')
COMPAT = 'theorem ite_eq_left : True := trivial\nalias Finset.prod_le_prod₀ := Finset.prod_le_prod\n'


def port(patches=(), ns='OAI', header=''):
    return O.module_files(O.module_sources(LEAN, ['OAI.Fam']), 'Solutions.F', patches, COMPAT, ns, header)


def test_nested_modules_flatten_and_imports_point_at_the_copies():
    files = port()
    assert sorted(files) == ['A.lean', 'Compat.lean', 'Main.lean', 'Sub_B.lean']
    assert files['Main.lean'].startswith('import Solutions.F.Sub_B\n')
    assert 'import Solutions.F.A\nimport Mathlib.Data.Nat.Basic\n' in files['Sub_B.lean']
    # only a module importing none of the copies imports Compat (the rest get it through them)
    assert files['A.lean'].startswith('import Mathlib\nimport Solutions.F.Compat\n')
    assert files['Sub_B.lean'].count('import Mathlib') == 1
    assert 'Compat' not in files['Sub_B.lean'] and 'Compat' not in files['Main.lean']


def test_linter_and_header_lines_go_after_the_imports():
    files = port(header='set_option maxHeartbeats 400000\n')
    ls = files['Sub_B.lean'].split('\n')
    k = max(i for i, l in enumerate(ls) if l.startswith('import '))
    assert ls[k + 2] == 'set_option linter.all false'
    assert 'set_option maxHeartbeats 400000' in ls[k + 2:k + 8]


def test_compat_module_is_namespaced_and_aliases_become_rewrites():
    files = port()
    assert files['Compat.lean'].startswith('import Mathlib\n\nnamespace OAI\n')
    assert 'alias' not in files['Compat.lean']
    assert 'Finset.prod_le_prod = Finset.prod_le_prod' in files['A.lean']
    root = port(ns=None)
    assert root['Compat.lean'] == 'import Mathlib\n\n' + COMPAT
    assert 'prod_le_prod₀' in root['A.lean']


def test_patches_count_over_all_modules():
    out = port([{'old': ':= trivial', 'new': ':= True.intro'}])
    assert 'True.intro' in out['Sub_B.lean']
    with pytest.raises(O.PortError, match='applies 0 times'):
        port([{'old': 'nowhere', 'new': 'x'}])
    with pytest.raises(O.PortError, match='applies 3 times, want 1'):
        port([{'old': 'namespace OAI.Fam', 'new': 'x'}])


def test_an_unported_openai_import_is_an_error():
    src = O.module_sources(LEAN, ['OAI.Fam'])
    short, t = src['OAI.Fam.Main']
    src['OAI.Fam.Main'] = (short, 'import OAI.Other.Thing\n' + t)
    with pytest.raises(O.PortError, match='OAI.Other.Thing'):
        O.module_files(src, 'Solutions.F', (), COMPAT)


def test_only_changed_files_are_rewritten(tmp_path):
    files = port()
    assert len(PM.write_changed(str(tmp_path), files)) == 4
    assert PM.write_changed(str(tmp_path), files) == []
    files['A.lean'] += '\n'
    assert PM.write_changed(str(tmp_path), files) == ['A.lean']


def test_build_order_and_elab_log(tmp_path):
    files = port()
    PM.write_changed(str(tmp_path), files)
    assert BM.module_order(str(tmp_path), 'Solutions.F', 'Main') == ['Compat', 'A', 'Sub_B', 'Main']
    log = '✔ [1/3] Built Solutions.F.A (12.5s)\n✔ [2/3] Replayed Solutions.F.B\n✔ [3/3] Built Solutions.F.C (2.0s)\n'
    assert BM.elab_lines(log, 3.0) == '✔ Built Solutions.F.A (9.50s)\n✔ Built Solutions.F.C (0.10s)\n'


def test_config_keeps_hand_set_keys_and_merges_build_logs(tmp_path):
    d = tmp_path
    (d / 'build_elab.log').write_text('✔ Built Solutions.F.A (10.0s)\n✔ Built Solutions.F.B (1.0s)\n')
    (d / 'build_elab_2.log').write_text('✔ Built Solutions.F.A (20.0s)\n')
    ws = tmp_path / 'ws'
    (ws / 'Definitions').mkdir(parents=True)
    (ws / 'Definitions' / 'Def_X.lean').write_text(open(os.path.join(FIX, 'bundle.lean')).read())
    old = {'patches': [{'old': 'a', 'new': 'b'}], 'pinned': ['P'], 'budget': 99}
    cfg = CP.make_config(str(d), 'F', 'Main', 'OAI.Fam.main', ['Definitions.Def_X'], 'FAM',
                         ['OAI.Fam.b_thm'], 40, 0.0, str(ws), old)
    assert cfg['patches'] == old['patches'] and cfg['pinned'] == ['P'] and cfg['budget'] == 40
    assert cfg['external_defs']['OAI.Glob.Hom.id'] == 'Definitions.Def_X'
    assert cfg['roots'] == ['Solutions.F.Main'] and cfg['external'] == ['OAI.Fam.main']
    adj = (d / 'build_adj.log').read_text()
    # HenonLaneEmden (2026-10-19): oai_build_modules --elab-log has already taken the import
    # overhead off; subtracting it again floored nearly every module and the cost model
    # underestimated pieces 5-7x. By default the times pass through unchanged
    assert 'Solutions.F.A (20.0s)' in adj and 'Solutions.F.B (1.0s)' in adj
    CP.make_config(str(d), 'F', 'Main', 'OAI.Fam.main', [], 'FAM', [], 40, 2.8, str(ws), None)
    adj = (d / 'build_adj.log').read_text()
    assert 'Solutions.F.A (17.2s)' in adj and 'Solutions.F.B (0.1s)' in adj


def test_external_defs_map_children_to_graph_owners():
    names = {'OAI.G.Hom': 'D', 'OAI.G.Hom.mk': 'D', 'OAI.G.absent': 'D'}
    owner = {'OAI.G.Hom.mk': 'OAI.G.Hom'}
    assert CP.graph_external_defs(names, owner, {'OAI.G.Hom': 1}) == {'OAI.G.Hom': 'D'}


def test_external_defs_map_private_nodes_to_published_names():
    # a `private def delta` is the graph node `_private.<module>.0.<name>`; the published bundle
    # (the carver drops `private`) declares plain `<name>`; without this the carve redeclared it
    # (oaiq-067: OAI.DilutedSpinGlass.FiniteLaw.delta)
    names = {'OAI.G.delta': 'D', 'OAI.G.other': 'D'}
    nodes = {'_private.Solutions.F.M.0.OAI.G.delta': 1, '_private.Solutions.F.M.0.OAI.G.mine': 1}
    assert CP.graph_external_defs(names, {}, nodes) == {'_private.Solutions.F.M.0.OAI.G.delta': 'D'}


def test_filter_patches_keeps_exact_counts():
    keep, drop = CP.filter_patches([{'old': 'x', 'new': 'y', 'count': 2}, {'old': 'z', 'new': 'w'}],
                                   ['x\n', 'x z z\n'])
    assert keep == [{'old': 'x', 'new': 'y', 'count': 2}]
    assert drop == [(2, {'old': 'z', 'new': 'w'})]
    # a chained patch (its `old` is an earlier patch's `new`) counts after the earlier ones
    chain = [{'old': 'a b', 'new': 'a c'}, {'old': 'a c', 'new': 'a d'}]
    keep, drop = CP.filter_patches(chain, ['a b\n'])
    assert keep == chain and drop == []


def test_filter_patches_refuses_a_patch_that_cuts_an_identifier():
    # oaiq-040: `... T 3 hpos` also matched the start of `hpositive`; with the count raised to fit, the
    # port wrote `hpos 3itive`, a parse error found after a 13 min rebuild
    p = {'old': 'pow_nonneg T 3 hpos', 'new': 'pow_nonneg T 3 hpos.le', 'count': 2}
    keep, drop = CP.filter_patches([p], ['pow_nonneg T 3 hpos)\n', 'pow_nonneg T 3 hpositive\n'])
    assert keep == [] and len(drop) == 1 and drop[0][0].startswith('cuts an identifier')
    assert 'hpositive' in drop[0][0]
    # a match at an identifier's start is caught too; delimiters on both sides are fine
    keep, drop = CP.filter_patches([{'old': 'pos_of', 'new': 'q'}], ['lt_pos_of x\n'])
    assert keep == [] and drop[0][0].startswith('cuts an identifier')
    keep, drop = CP.filter_patches([{'old': 'hpos)', 'new': 'hpos.le)'}], ['f (hpos)\n'])
    assert drop == []
    keep, drop = CP.filter_patches([{'old': '(hpos', 'new': '(hpos.le'}], ['f (hpos)\n'])
    assert drop == []


def test_text_check_names_and_stub_comments():
    md = '---\nsource: `a/b`\n---\nUses `Foo.bar_baz` and `qux_lemma h` and `Mathlib_thing`.\n'
    lib = {'Mathlib_thing'}
    bad = CP.missing_names(md, 'theorem bar_baz : True', lambda n: n in lib)
    assert bad == ['qux_lemma']
    assert CP.stub_comments({'Thm_A.lean': 'theorem a : True', 'Thm_B.lean': '-- note\ntheorem b'}) == ['Thm_B.lean']


def test_bundle_prose_fills_the_template(tmp_path):
    (tmp_path / 'Def_FAM000.lean').write_text('-- module Solutions.F.A\n-- module Solutions.F.Compat\n')
    (tmp_path / 'extra_FAM000.md').write_text('More.')
    plan = {'bundles': [{'name': 'FAM000', 'imports': ['FAM001']}]}
    out = CP.bundle_prose(plan, str(tmp_path), '{NAME}: {MODULES}. {IMPORTS} {EXTRA}', str(tmp_path))
    assert out == {'FAM000': 'FAM000: `A`. It also imports the bundle `FAM001` of this split. More.'}


def test_measure_copies_every_imported_published_module(tmp_path):
    import carve_measure as M
    cfg = {'external_defs': {'a': 'Definitions.Def_X'}, 'external_theorems': {'t': 'Theorems.Thm_T'},
           'extra_olean_modules': ['Definitions.Def_Y']}
    plan = {'external': ['OAI.F.main']}
    assert M.imported_modules(cfg, plan) == ['Definitions.Def_X', 'Definitions.Def_Y',
                                             'Theorems.Thm_OAI_F_main', 'Theorems.Thm_T']
    # a module missing from the workspace build but already in the private dir (a core split) is kept
    ws, ol = tmp_path / 'ws', tmp_path / 'olean'
    (ol / 'Definitions').mkdir(parents=True)
    (ol / 'Definitions' / 'Def_Core.olean').write_text('x')
    (ol / 'Definitions' / 'Def_Core.ilean').write_text('x')
    M.copy_published(str(ws), str(ol), ['Definitions.Def_Core'])
    with pytest.raises(SystemExit):
        M.copy_published(str(ws), str(ol), ['Definitions.Def_Missing'])


def test_publish_prep_writes_run_files_and_manifest(tmp_path, monkeypatch):
    for x in ('out/lib', 'out/solutions', 'work'):
        (tmp_path / x).mkdir(parents=True)
    (tmp_path / 'out/lib/Def_A.lean').write_text('a')
    (tmp_path / 'out/solutions/Sol_B.lean').write_text('b')
    plan = {'bundles': [{'name': 'A', 'imports': [], 'nodes': ['x']}], 'stubs': {},
            'pieces': {'B': {'bundles': ['A'], 'imports': []}}, 'external': ['B']}
    (tmp_path / 'work' / 'plan.json').write_text(json.dumps(plan))
    (tmp_path / 'work' / 'times.json').write_text('{}')
    # HenonLaneEmden (2026-10-19): no work/order.json yet (carve.py order not run): computed here
    monkeypatch.chdir(str(tmp_path))
    P, man = CP.publish_prep('.', 'src', ['t1', 't2'])
    # the run files name absolute paths: split_run runs from anywhere
    assert os.path.isabs(json.load(open(os.path.join(P, 'run.json')))['plan'])
    assert json.load(open(os.path.join(P, 'run_2_statements.json')))['kinds'] == ['statement']
    assert json.load(open(os.path.join(P, 'run.json')))['tags'] == ['t1', 't2']
    assert man.splitlines()[0].endswith('  out/lib/Def_A.lean') and len(man.splitlines()) == 2
    assert json.load(open(os.path.join(P, 'order.json')))['waves'] == [['bundle:A'], ['piece:B']]
    # an unmeasured carve is refused with the step to run
    os.remove(str(tmp_path / 'work' / 'times.json'))
    with pytest.raises(SystemExit, match='carve_measure'):
        CP.publish_prep('.', 'src', ['t1'])


def test_ext_defs_ask_lean_for_a_bundle_with_anonymous_instances(tmp_path, monkeypatch):
    # DiamondDistortion (2026-10-19): Def_DiamondDistortion's anonymous instances have
    # Lean-generated names (SegmentSystem.instNonemptyFamily) that the source parse cannot see;
    # missing from external_defs, the port's copies were carved into our bundle and clashed
    ws = tmp_path / 'ws'
    (ws / 'Definitions').mkdir(parents=True)
    (ws / 'Definitions' / 'Def_A.lean').write_text('namespace X\ndef f : Nat := 1\nend X\n')
    (ws / 'Definitions' / 'Def_B.lean').write_text('namespace X\ninstance : Nonempty Nat := ⟨0⟩\nend X\n')
    asked = []

    def fake(ws_, m):
        asked.append(m)
        return ['X.instNonemptyNat']
    monkeypatch.setattr(CP, 'lean_constants', fake)
    names = CP.bundle_constants(str(ws), ['Definitions.Def_A', 'Definitions.Def_B'])
    assert asked == ['Definitions.Def_B']
    assert names == {'X.f': 'Definitions.Def_A', 'X.instNonemptyNat': 'Definitions.Def_B'}


# ---------------------------------------------------------------- patches, counted as the port sees them

TENSOR = ('import Mathlib\n\nnamespace OAI.Fam\n\ntheorem t (x : M ⊗[R] N) : f x = 0 := by\n'
          '  induction x using TensorProduct.inductionOn with\n  | tmul a b => simp\n'
          '  | add a b ha hb => simp [ha, hb]\n\nend OAI.Fam\n')
UNIV = ('import Mathlib\n\nuniverse uA uB\n\nnamespace OAI.Fam\n\n'
        'def useSys : Sys.{uA, uB} := sorry\n\nend OAI.Fam\n')


def _sources():
    src = O.module_sources(LEAN, ['OAI.Fam'])
    src['OAI.Fam.T'] = ('T', TENSOR)
    src['OAI.Fam.U'] = ('U', UNIV)
    return src


def test_filter_patches_counts_against_the_text_the_module_port_patches():
    # ComparatorModel (2026-10-24): filter-patches counted against OpenAI's raw source, where the
    # `| zero => simp only [map_zero]` the port's core rewrite then inserted did not occur yet:
    # dropped (0 occurrences), the build failed (the rewrite now names `OAI.tensorInductionOn`).
    # CubeShuffle: `Finset.prod_le_one₀` is rewritten by the compat aliases before the patches
    # run, so its patch no longer applies: kept, the port failed.
    pz = {'old': 'using OAI.tensorInductionOn with', 'new': 'using OAI.tensorInductionOn with'}
    pa = {'old': 'Finset.prod_le_prod₀ = Finset.prod_le_prod₀', 'new': 'x'}
    keep, drop = CP.port_filter_patches([pz, pa], _sources(), COMPAT, 'OAI')
    assert keep == [pz]
    assert drop == [(0, pa)]
    # what is kept applies cleanly on the module route
    O.module_files(_sources(), 'Solutions.F', keep, COMPAT)


def test_filter_patches_drops_single_file_only_patches():
    # WLTime (2026-10-23): merge.py's single `universe` line orders a declaration's universe
    # parameters, so the single-file port needed `Sys.{uA, uB}` -> `Sys.{uB, uA}`; in a module the
    # module's own `universe` line rules, the patch still matched once, and the build failed.
    pu = {'old': 'Sys.{uA, uB}', 'new': 'Sys.{uB, uA}'}
    ps = {'old': 'theorem b_thm', 'new': 'theorem b_thm', 'route': 'single'}
    pm = {'old': 'theorem b_thm', 'new': 'theorem b_thm\'', 'route': 'modules'}
    keep, drop = CP.port_filter_patches([pu, ps, pm], _sources(), COMPAT, 'OAI')
    assert keep == [pm]
    assert drop == [('single-file only', pu), ('single-file only', ps)]
    # the module port itself never applies them, and the single-file route skips module-only ones
    out = O.module_files(_sources(), 'Solutions.F', [pu, ps, pm], COMPAT)
    assert 'Sys.{uA, uB}' in out['U.lean'] and "b_thm'" in out['Sub_B.lean']
    assert O.apply_patches('theorem b_thm', [pm], route='single') == 'theorem b_thm'


def test_filter_patches_accepts_compat_imports_option(tmp_path):
    # carve_pipeline passes the port's `--compat-imports narrow` to filter-patches too (oaiq-092): its
    # value is not a module prefix
    p = tmp_path / 'p.json'
    p.write_text(json.dumps([{'old': 'theorem b_thm', 'new': 'theorem b_thm'}]))
    c = tmp_path / 'compat.lean'
    c.write_text(COMPAT)
    out = tmp_path / 'out.json'
    CP.main(['filter-patches', str(p), LEAN, str(out), 'OAI.Fam', '--compat', str(c),
             '--compat-imports', 'narrow'])
    assert len(json.load(open(str(out)))) == 1


def test_filter_patches_command_line(tmp_path):
    p = tmp_path / 'p.json'
    p.write_text(json.dumps([{'old': 'Finset.prod_le_prod₀ = Finset.prod_le_prod₀', 'new': 'x', 'allow_drop': True},
                             {'old': 'theorem b_thm', 'new': 'theorem b_thm'}]))
    c = tmp_path / 'compat.lean'
    c.write_text(COMPAT)
    out = tmp_path / 'out.json'
    CP.main(['filter-patches', str(p), LEAN, str(out), 'OAI.Fam', '--compat', str(c)])
    assert json.load(open(str(out))) == [{'old': 'theorem b_thm', 'new': 'theorem b_thm'}]
    # with the root-level compat block the alias is not rewritten, so the first patch applies
    CP.main(['filter-patches', str(p), LEAN, str(out), 'OAI.Fam', '--compat', str(c), '--root-compat'])
    assert len(json.load(open(str(out)))) == 2


def test_filter_patches_command_fails_on_a_dropped_patch_unless_it_may_drop(tmp_path, capsys):
    # six batches missed the one-line `dropped (N occurrences)` and ran an unpatched port
    c = tmp_path / 'compat.lean'
    c.write_text(COMPAT)
    out = tmp_path / 'out.json'
    p = tmp_path / 'p.json'
    bad = {'old': 'theorem b_thm', 'new': 'theorem b_thm\'', 'count': 3}
    p.write_text(json.dumps([{'old': 'theorem b_thm', 'new': 'theorem b_thm'}, bad]))
    with pytest.raises(SystemExit) as e:
        CP.main(['filter-patches', str(p), LEAN, str(out), 'OAI.Fam', '--compat', str(c)])
    assert 'dropped' in str(e.value) and not out.exists()
    err = capsys.readouterr().err
    assert 'expected count 3' in err and 'found 1' in err and 'B' in err and 'theorem b_thm' in err
    # a patch matching nowhere is reported as such
    p.write_text(json.dumps([{'old': 'no such text', 'new': 'x'}]))
    with pytest.raises(SystemExit):
        CP.main(['filter-patches', str(p), LEAN, str(out), 'OAI.Fam', '--compat', str(c)])
    assert 'none in any module' in capsys.readouterr().err
    # allowed to drop, or deliberately single-file-only: kept going
    p.write_text(json.dumps([dict(bad, allow_drop=True), {'old': 'Sys.{uA, uB}', 'new': 'x', 'route': 'single'}]))
    CP.main(['filter-patches', str(p), LEAN, str(out), 'OAI.Fam', '--compat', str(c)])
    assert json.load(open(str(out))) == []


MACRO_DEF = ('import Mathlib\n\nnamespace OAI.Fam\n\n/-- Closes word goals.  Each leaf is\nproved. -/\n'
             'macro "word_poly" : tactic => `(tactic|\n  repeat\' first\n  | rfl\n  | simp)\n\n'
             'theorem m1 : 1 = 1 := by word_poly\n\nend OAI.Fam\n')
MACRO_USE = ('import OAI.Fam.M\n\nnamespace OAI.Fam\n\ntheorem m2 : 2 = 2 := by\n  word_poly\n\n'
             'theorem m3 (word_poly\' : Nat) : True := trivial\n\nend OAI.Fam\n')


def test_module_port_inlines_tactic_macros_across_modules():
    # WLIdentification (2026-10-23): the module route kept OpenAI's `macro "word_poly"`, which
    # carve.py gen refuses (the verifier rejects any macro), while oai_port.py inlines macros. A
    # macro is inlined in its own module and in every module importing it, and its doc comment goes
    # with it (left behind, it dangled before the next command)
    src = O.module_sources(LEAN, ['OAI.Fam'])
    src['OAI.Fam.M'] = ('M', MACRO_DEF)
    src['OAI.Fam.N'] = ('N', MACRO_USE)
    src['OAI.Fam.P'] = ('P', 'import Mathlib\n\nnamespace OAI.Fam.P\ntheorem word_poly : True := trivial\nend OAI.Fam.P\n')
    files = O.module_files(src, 'Solutions.F', (), COMPAT)
    body = "(repeat' first | rfl | simp)"
    assert 'macro' not in files['M.lean'] and 'Closes word goals' not in files['M.lean']
    assert 'theorem m1 : 1 = 1 := by %s\n' % body in files['M.lean']
    assert 'theorem m2 : 2 = 2 := by\n  %s\n' % body in files['N.lean']
    assert "(word_poly' : Nat)" in files['N.lean']
    # a module that does not import the macro's module keeps its own meaning of the name
    assert 'theorem word_poly : True' in files['P.lean']


def _fake_lean(monkeypatch, built):
    import subprocess
    # the plain `lean -o` path: no compiled LeanInfo (leaninfo.build_module then returns None)
    monkeypatch.setenv('P2M_LEANINFO_INTERPRETED', '1')

    def run(args, **kw):
        out = args[args.index('-o') + 1]
        open(out, 'w').write('olean')
        open(args[args.index('-i') + 1], 'w').write('ilean')
        built.append(os.path.basename(out)[:-6])
        return subprocess.CompletedProcess(args, 0, '', '')
    monkeypatch.setattr(BM.subprocess, 'run', run)


def test_build_rebuilds_the_dependents_of_a_changed_module(tmp_path, monkeypatch):
    # Problem340 (2026-10-24): a module was rebuilt only when its own source was newer than its
    # .olean, so after a fix to a module its importers kept stale .oleans (a --force rebuild was
    # needed). A module is stale when its source or any imported module's .olean is newer.
    ws = tmp_path
    d = ws / 'Solutions' / 'F'
    d.mkdir(parents=True)
    (d / 'A.lean').write_text('import Mathlib\n')
    (d / 'B.lean').write_text('import Solutions.F.A\n')
    (d / 'C.lean').write_text('import Mathlib\n')
    (d / 'Main.lean').write_text('import Solutions.F.B\nimport Solutions.F.C\n')
    built = []
    _fake_lean(monkeypatch, built)
    assert BM.build(str(ws), 'F', 'Main')[0] and built == ['A', 'B', 'C', 'Main']
    out = ws / '.lake' / 'build' / 'lib' / 'lean' / 'Solutions' / 'F'
    t0 = os.path.getmtime(str(out / 'Main.olean'))
    for m in ('A', 'B', 'C', 'Main'):
        os.utime(str(out / (m + '.olean')), (t0 - 100, t0 - 100))
        os.utime(str(d / (m + '.lean')), (t0 - 200, t0 - 200))
    del built[:]
    assert BM.build(str(ws), 'F', 'Main')[0] and built == []
    os.utime(str(d / 'A.lean'), (t0, t0))            # A edited: B and Main import it, C does not
    del built[:]
    assert BM.build(str(ws), 'F', 'Main')[0] and built == ['A', 'B', 'Main']
    # an import rebuilt in an earlier run (its importer's build failed, or ran elsewhere)
    for m in ('A', 'B', 'C', 'Main'):
        os.utime(str(out / (m + '.olean')), (t0 - 100, t0 - 100))
    os.utime(str(d / 'A.lean'), (t0 - 200, t0 - 200))
    os.utime(str(out / 'C.olean'), (t0, t0))
    del built[:]
    assert BM.build(str(ws), 'F', 'Main')[0] and built == ['Main']


# ---------------------------------------------------------------- the StdSimplex shim, module route

def simplex_sources():
    src = O.module_sources(LEAN, ['OAI.Fam'])
    short, t = src['OAI.Fam.A']
    src['OAI.Fam.A'] = (short, t.replace('import Mathlib\n', 'import Mathlib\nimport Mathlib.Geometry.Convex.ConvexSpace.Barycenter\n')
                        + 'theorem s (n : ℕ) : Nonempty (Convexity.StdSimplex ℝ (Fin (n+1))) := inferInstance\n')
    return src


def test_module_route_adds_the_stdsimplex_shim_module_where_it_is_used():
    files = O.module_files(simplex_sources(), 'Solutions.F', (), COMPAT)
    assert files['StdSimplexCompat.lean'] == O.stdsimplex_shim()
    a = files['A.lean']
    # Compat still imported (the shim import is not a ported OpenAI module), the shim too, the
    # d13f23b-only Mathlib import gone, the names kept (structure mode)
    assert 'import Solutions.F.Compat\n' in a and 'import Solutions.F.StdSimplexCompat\n' in a
    assert 'ConvexSpace.Barycenter' not in a and 'Convexity.StdSimplex ℝ' in a
    assert 'StdSimplexCompat' not in files['Sub_B.lean'] and 'StdSimplexCompat' not in files['Main.lean']
    sub = O.module_files(simplex_sources(), 'Solutions.F', (), COMPAT, stdsimplex='subtype')
    assert 'Nonempty (OAI.SStd ℝ (Fin (n+1)))' in sub['A.lean']
    off = O.module_files(simplex_sources(), 'Solutions.F', (), COMPAT, stdsimplex='off')
    assert 'StdSimplexCompat.lean' not in off and 'ConvexSpace.Barycenter' in off['A.lean']
    # nothing mentions it: no shim
    assert 'StdSimplexCompat.lean' not in port()


def test_filter_patches_sees_the_stdsimplex_rewrite():
    src = simplex_sources()
    p = [{'old': 'Nonempty (OAI.SStd ℝ', 'new': 'Nonempty (OAI.SStd ℝ'}]
    keep, _ = CP.port_filter_patches(p, src, COMPAT, stdsimplex='subtype')
    assert keep == p
    keep, _ = CP.port_filter_patches(p, src, COMPAT)
    assert keep == []


def test_config_imports_the_published_shim_bundle(tmp_path):
    d = tmp_path
    ws = tmp_path / 'ws'
    (ws / 'Definitions').mkdir(parents=True)
    (ws / 'Solutions' / 'F').mkdir(parents=True)
    (ws / 'Solutions' / 'F' / 'StdSimplexCompat.lean').write_text(O.stdsimplex_shim())
    cfg = CP.make_config(str(d), 'F', 'Main', 'OAI.Fam.main', [], 'FAM', [], 40, 0.0, str(ws), None)
    assert O.STDSIMPLEX_BUNDLE not in set(cfg['external_defs'].values())   # not published locally
    (ws / 'Definitions' / (O.STDSIMPLEX_BUNDLE.split('.')[-1] + '.lean')).write_text(O.stdsimplex_shim())
    cfg = CP.make_config(str(d), 'F', 'Main', 'OAI.Fam.main', [], 'FAM', [], 40, 0.0, str(ws), None)
    assert cfg['external_defs']['Convexity.StdSimplex.homeomorphI'] == O.STDSIMPLEX_BUNDLE
    assert cfg['external_defs']['OAI.SStd.map'] == O.STDSIMPLEX_BUNDLE


@pytest.mark.lean
def test_stdsimplex_shim_compiles_and_covers_openai_names(tmp_path):
    import subprocess
    from p2mlib.workspace import workspace
    f = tmp_path / 'Shim.lean'
    checks = ''.join('#check @Convexity.%s\n' % n for n in O.OAI_STDSIMPLEX_NAMES)
    checks += 'example : CompactSpace (Convexity.StdSimplex ℝ (Fin 3)) := inferInstance\n'
    checks += 'example : PathConnectedSpace (Convexity.StdSimplex ℝ ℕ) := inferInstance\n'
    checks += '#check @OAI.SStd.isEmbedding_toFun_comp_weights\n'
    f.write_text(O.stdsimplex_shim() + '\n' + checks)
    r = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false', str(f)], cwd=workspace(),
                       capture_output=True, text=True)
    out = r.stdout + r.stderr
    assert r.returncode == 0 and 'error' not in out, out[-3000:]
    assert 'sorry' not in out


def test_text_check_skips_auto_named_instances():
    md = 'Uses `Ns.Specht.instFintypeTabloid` and `Ns.instDecidableEqSwitchIndex`.\n'
    assert CP.missing_names(md, 'noncomputable instance : Fintype (Tabloid m) := x', lambda n: False) == []


def test_measure_never_leaves_an_old_olean_behind_a_failed_compile(tmp_path, monkeypatch):
    # oaiq-065: after a re-plan, Def_OAIQ65Sa010 failed to compile, and the previous plan's .olean of that
    # name stayed in D/olean; with --keep-going later bundles compiled against that different bundle
    # ("Unknown constant", "Unknown identifier"). The outputs go before each compile.
    import carve_measure as M
    m = object.__new__(M.Measure)
    m.olean, m.stage, m.lean_ws = str(tmp_path / 'olean'), str(tmp_path / 'stage'), str(tmp_path)
    old = tmp_path / 'olean' / 'Definitions' / 'Def_B010'
    old.parent.mkdir(parents=True)
    for ext in ('.olean', '.ilean'):
        (old.parent / ('Def_B010' + ext)).write_text('the previous plan')
    src = tmp_path / 'Def_B010.lean'
    src.write_text('broken')

    class R:
        returncode, stdout, stderr = 1, 'Def_B010.lean:1:0: error: oops', ''
    monkeypatch.setattr(M.subprocess, 'run', lambda *a, **k: R())
    res, _ = m.run(str(src), 'Definitions.Def_B010', {})
    assert not res['ok']
    assert not (old.parent / 'Def_B010.olean').exists() and not (old.parent / 'Def_B010.ilean').exists()
