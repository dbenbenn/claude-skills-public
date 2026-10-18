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
                         ['OAI.Fam.b_thm'], 40, 2.8, str(ws), old)
    assert cfg['patches'] == old['patches'] and cfg['pinned'] == ['P'] and cfg['budget'] == 40
    assert cfg['external_defs']['OAI.Glob.Hom.id'] == 'Definitions.Def_X'
    assert cfg['roots'] == ['Solutions.F.Main'] and cfg['external'] == ['OAI.Fam.main']
    adj = (d / 'build_adj.log').read_text()
    assert 'Solutions.F.A (17.2s)' in adj and 'Solutions.F.B (0.6s)' in adj


def test_external_defs_map_children_to_graph_owners():
    names = {'OAI.G.Hom': 'D', 'OAI.G.Hom.mk': 'D', 'OAI.G.absent': 'D'}
    owner = {'OAI.G.Hom.mk': 'OAI.G.Hom'}
    assert CP.graph_external_defs(names, owner, {'OAI.G.Hom': 1}) == {'OAI.G.Hom': 'D'}


def test_filter_patches_keeps_exact_counts():
    keep, drop = CP.filter_patches([{'old': 'x', 'new': 'y', 'count': 2}, {'old': 'z', 'new': 'w'}],
                                   ['x\n', 'x z z\n'])
    assert keep == [{'old': 'x', 'new': 'y', 'count': 2}]
    assert drop == [(2, {'old': 'z', 'new': 'w'})]


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


def test_publish_prep_writes_run_files_and_manifest(tmp_path):
    for x in ('out/lib', 'out/solutions', 'work'):
        (tmp_path / x).mkdir(parents=True)
    (tmp_path / 'out/lib/Def_A.lean').write_text('a')
    (tmp_path / 'out/solutions/Sol_B.lean').write_text('b')
    for f in ('plan.json', 'order.json', 'times.json'):
        (tmp_path / 'work' / f).write_text('{}')
    P, man = CP.publish_prep(str(tmp_path), 'src', ['t1', 't2'])
    assert json.load(open(os.path.join(P, 'run_2_statements.json')))['kinds'] == ['statement']
    assert json.load(open(os.path.join(P, 'run.json')))['tags'] == ['t1', 't2']
    assert man.splitlines()[0].endswith('  out/lib/Def_A.lean') and len(man.splitlines()) == 2
