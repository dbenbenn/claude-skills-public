"""carve_measure.py's state files (atomic writes, truncated-file recovery) and its import-closure report.

q149 / oaiq-106 (2026-11): a disk-full crash cut work/times.json mid-entry (888 KB); and every bundle the
platform published had an import closure (the .olean bytes of its transitive Solutions/Definitions/
Theorems imports) of at most 0.74 GB, while D186 at 0.87 GB timed out 30+ times.
"""
import json
import os

import pytest


def _obj(tmp_path, plan):
    import carve_measure as M
    m = object.__new__(M.Measure)
    for x in ('lib', 'sol', 'work', 'olean', 'stage', 'chk', 'ws'):
        (tmp_path / x).mkdir(exist_ok=True)
    m.lib, m.sol, m.olean, m.stage, m.chk = (str(tmp_path / x) for x in ('lib', 'sol', 'olean', 'stage', 'chk'))
    m.d, m.ws, m.lean_ws = str(tmp_path), str(tmp_path / 'ws'), str(tmp_path)
    m.cfg = {'work': str(tmp_path / 'work')}
    m.plan, m.ext, m.times, m.repairs, m.edges = plan, set(), {}, {}, {}
    m.times_path = str(tmp_path / 'work' / 'times.json')
    m.rp_path = str(tmp_path / 'work' / 'repairs.json')
    m.edges_path = str(tmp_path / 'work' / 'edges.json')
    m.bundle_names = [b['name'] for b in plan.get('bundles', [])]
    m.allow_false = False
    m.env = lambda: {}
    return M, m


def _olean(root, module, size):
    p = os.path.join(str(root), *module.split('.')) + '.olean'
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, 'wb') as f:
        f.write(b'\0' * size)
    return p


# ------------------------------------------------------------- atomic state files

def test_write_json_replaces_the_file_whole_and_leaves_no_temporary(tmp_path):
    import carve_measure as M
    p = tmp_path / 'times.json'
    M.write_json(str(p), {'bundle:B': {'secs': 1.0}}, indent=1)
    assert json.loads(p.read_text()) == {'bundle:B': {'secs': 1.0}}
    assert os.listdir(tmp_path) == ['times.json']


def test_a_write_that_fails_midway_keeps_the_previous_file(tmp_path):
    # q149: a disk-full crash during json.dump left times.json cut mid-entry; writing to a temporary
    # file and renaming it keeps the last complete file whatever happens mid-write
    import carve_measure as M
    p = tmp_path / 'times.json'
    M.write_json(str(p), {'bundle:A': {'secs': 1.0}})
    with pytest.raises(TypeError):
        M.write_json(str(p), {'bundle:A': {'secs': 1.0}, 'bundle:B': object()})
    assert json.loads(p.read_text()) == {'bundle:A': {'secs': 1.0}}
    assert os.listdir(tmp_path) == ['times.json']


def test_a_truncated_state_file_keeps_its_complete_entries_and_the_original(tmp_path, capsys):
    import carve_measure as M
    p = tmp_path / 'times.json'
    full = json.dumps({'bundle:A': {'secs': 1.0, 'ok': True, 'errors': []},
                       'bundle:B': {'secs': 2.0, 'ok': True, 'errors': ['x, y: "z"}']},
                       'bundle:C': {'secs': 3.0, 'ok': False, 'errors': []}}, indent=1)
    cut = full[:full.index('"bundle:C"') + 30]                 # cut mid-entry, as the disk-full crash did
    p.write_text(cut)
    got = M.load_json(str(p), {})
    assert got == {'bundle:A': {'secs': 1.0, 'ok': True, 'errors': []},
                   'bundle:B': {'secs': 2.0, 'ok': True, 'errors': ['x, y: "z"}']}}
    assert (tmp_path / 'times.json.truncated').read_text() == cut      # the original, kept
    assert json.loads(p.read_text()) == got                            # repaired in place
    err = capsys.readouterr().err
    assert 'times.json' in err and 'times.json.truncated' in err and '2 complete entries' in err
    # a second truncation never overwrites the first original
    p.write_text(cut)
    M.load_json(str(p), {})
    assert (tmp_path / 'times.json.truncated.1').read_text() == cut


def test_a_missing_state_file_is_the_default_and_an_unreadable_one_stops_with_the_repair(tmp_path):
    import carve_measure as M
    assert M.load_json(str(tmp_path / 'none.json'), {}) == {}
    bad = tmp_path / 'edges.json'
    bad.write_text('[1, 2')                                    # not an object: nothing to recover
    with pytest.raises(SystemExit) as e:
        M.load_json(str(bad), {})
    assert 'edges.json' in str(e.value) and 'partial entry' in str(e.value)


def test_recover_object_stops_at_the_first_incomplete_entry():
    import carve_measure as M
    assert M.recover_object('{\n "a": [1],\n "b": {"c": "d"},\n "e": ["f", "g') == {'a': [1], 'b': {'c': 'd'}}
    assert M.recover_object('{\n "a": 1,\n "b"') == {'a': 1}
    assert M.recover_object('{') == {}
    assert M.recover_object('[1]') is None


def test_run_all_writes_times_json_atomically(tmp_path, monkeypatch):
    plan = {'bundles': [{'name': 'A', 'imports': [], 'nodes': ['x']}], 'stubs': {}, 'pieces': {}, 'external': []}
    M, m = _obj(tmp_path, plan)
    writes = []
    real = M.write_json
    monkeypatch.setattr(M, 'write_json', lambda path, obj, **kw: writes.append(os.path.basename(path)) or real(path, obj, **kw))
    monkeypatch.setattr(M, 'copy_published', lambda *a: None)
    m.measure = lambda item, env, force, repair: {'secs': 1.0, 'ok': True, 'errors': []}
    m.edge_check = lambda item, env, force: {'imports': {}, 'false': [], 'restore': {}, 'file': 'f'}
    assert m.run_all()
    assert 'times.json' in writes and 'false_edges.json' in writes
    assert json.load(open(m.times_path))['bundle:A']['ok']


# ------------------------------------------------------------- the import closure

def test_import_closure_sums_the_transitive_carve_and_published_oleans_once_each(tmp_path):
    # Mathlib is not counted; a module reached twice (a diamond) counts once; the item's own .olean
    # is not part of its closure; a published module's .olean may sit in the workspace build
    M, m = _obj(tmp_path, {'bundles': []})
    lib = tmp_path / 'lib'
    (lib / 'Def_A.lean').write_text('import Mathlib\n')
    (lib / 'Def_B.lean').write_text('import Mathlib\nimport Definitions.Def_A\nimport Theorems.Thm_P\n')
    (lib / 'Def_C.lean').write_text('import Definitions.Def_A\n')
    (lib / 'Def_D.lean').write_text('import Mathlib\nimport Definitions.Def_B\nimport Definitions.Def_C\n')
    (tmp_path / 'ws' / 'Theorems').mkdir()
    (tmp_path / 'ws' / 'Theorems' / 'Thm_P.lean').write_text('import Mathlib\nimport Solutions.F.Base\n')
    (tmp_path / 'ws' / 'Solutions' / 'F').mkdir(parents=True)
    (tmp_path / 'ws' / 'Solutions' / 'F' / 'Base.lean').write_text('import Mathlib\n')
    for mod, size in (('Definitions.Def_A', 100), ('Definitions.Def_B', 20), ('Definitions.Def_C', 3),
                      ('Definitions.Def_D', 5000)):
        _olean(tmp_path / 'olean', mod, size)
    wb = tmp_path / 'ws' / '.lake' / 'build' / 'lib' / 'lean'
    _olean(wb, 'Theorems.Thm_P', 400)
    _olean(wb, 'Solutions.F.Base', 7000)
    _olean(wb, 'Mathlib', 10 ** 6)
    m.item_files = lambda kind, n: (str(lib / ('Def_%s.lean' % n)), 'Definitions.Def_' + n)
    r = m.import_closure('bundle:D')
    assert r == {'closure_bytes': 100 + 20 + 3 + 400 + 7000, 'closure_modules': 5}
    assert m.import_closure('bundle:A') == {'closure_bytes': 0, 'closure_modules': 0}


def test_import_closure_reports_modules_without_an_olean(tmp_path):
    M, m = _obj(tmp_path, {'bundles': []})
    lib = tmp_path / 'lib'
    (lib / 'Def_A.lean').write_text('import Mathlib\n')
    (lib / 'Def_B.lean').write_text('import Definitions.Def_A\nimport Definitions.Def_Gone\n')
    _olean(tmp_path / 'olean', 'Definitions.Def_A', 10)
    m.item_files = lambda kind, n: (str(lib / ('Def_%s.lean' % n)), 'Definitions.Def_' + n)
    assert m.import_closure('bundle:B') == {'closure_bytes': 10, 'closure_modules': 2, 'closure_missing': 1}


def test_a_pieces_closure_is_its_verifier_form_files(tmp_path):
    # the verifier compiles solution + statement together: the closure is the Chk file's imports
    M, m = _obj(tmp_path, {'bundles': [], 'stubs': {'A.t': {}}, 'statement_suffix': ''})
    (tmp_path / 'chk' / 'Chk_A_t.lean').write_text('import Mathlib\nimport Definitions.Def_S\nimport Theorems.Thm_U\n')
    (tmp_path / 'lib' / 'Def_S.lean').write_text('import Mathlib\n')
    (tmp_path / 'lib' / 'Thm_U.lean').write_text('import Definitions.Def_S\n')
    _olean(tmp_path / 'olean', 'Definitions.Def_S', 30)
    _olean(tmp_path / 'olean', 'Theorems.Thm_U', 4)
    assert m.import_closure('piece:A.t') == {'closure_bytes': 34, 'closure_modules': 2}


def test_measure_records_the_closure_beside_the_time_also_when_cached(tmp_path):
    M, m = _obj(tmp_path, {'bundles': [{'name': 'B', 'imports': ['A'], 'nodes': ['x']}]})
    lib = tmp_path / 'lib'
    (lib / 'Def_A.lean').write_text('import Mathlib\n')
    src = lib / 'Def_B.lean'
    src.write_text('import Mathlib\nimport Definitions.Def_A\n')
    _olean(tmp_path / 'olean', 'Definitions.Def_A', 64)
    m.item_files = lambda kind, n: (str(lib / ('Def_%s.lean' % n)), 'Definitions.Def_' + n)
    m.apply_recorded = lambda s: None
    calls = []

    def run(path, module, env):
        calls.append(module)
        _olean(tmp_path / 'olean', module, 1)
        return {'secs': 1.0, 'ok': True, 'errors': [], 'axioms': []}, ''
    m.run = run
    m.times['bundle:B'] = r = m.measure('bundle:B', {})
    assert r['closure_bytes'] == 64 and r['closure_modules'] == 1 and r['secs'] == 1.0
    del m.times['bundle:B']['closure_bytes']                  # a record from before the closure report
    r = m.measure('bundle:B', {})
    assert len(calls) == 1 and r['closure_bytes'] == 64      # cached, and its closure filled in


def test_run_all_warns_on_a_closure_over_the_soft_limit_and_never_fails_on_it(tmp_path, monkeypatch, capsys):
    plan = {'bundles': [{'name': 'A', 'imports': [], 'nodes': ['x']}, {'name': 'B', 'imports': [], 'nodes': ['y']}],
            'stubs': {}, 'pieces': {}, 'external': []}
    M, m = _obj(tmp_path, plan)
    assert M.CLOSURE_WARN_BYTES == 700 * 10 ** 6
    monkeypatch.setattr(M, 'copy_published', lambda *a: None)
    big = {'A': 10 ** 8, 'B': 87 * 10 ** 7}
    m.measure = lambda item, env, force, repair: {'secs': 1.0, 'ok': True, 'errors': [],
                                                  'closure_bytes': big[item.split(':')[1]], 'closure_modules': 39}
    m.edge_check = lambda item, env, force: {'imports': {}, 'false': [], 'restore': {}, 'file': 'f'}
    assert m.run_all()
    out = capsys.readouterr().out
    warn = [l for l in out.split('\n') if l.lstrip().startswith('WARNING import closure')]
    assert len(warn) == 1 and 'bundle:B' in warn[0] and '0.87 GB' in warn[0] and '0.7 GB' in warn[0]
    summary = [l for l in out.split('\n') if l.startswith('import closure over 0.7 GB')]
    assert len(summary) == 1 and '1 item' in summary[0] and 'bundle:B 0.87 GB' in summary[0]
    assert out.rstrip().split('\n')[-1] != 'FAILED'
    assert json.load(open(m.times_path))['bundle:B']['closure_bytes'] == 87 * 10 ** 7


def test_only_measures_just_the_named_items(tmp_path, monkeypatch):
    # carve_pipeline measures the pieces bundles wait for first (q153)
    plan = {'bundles': [{'name': 'A', 'imports': [], 'nodes': ['x']}], 'stubs': {'P': {'bundles': ['A']}, 'Q': {'bundles': ['A']}},
            'pieces': {'P': {'bundles': ['A'], 'imports': []}, 'Q': {'bundles': ['A'], 'imports': []}}, 'external': []}
    M, m = _obj(tmp_path, plan)
    monkeypatch.setattr(M, 'copy_published', lambda *a: None)
    seen = []
    m.measure = lambda item, env, force, repair: seen.append(item) or {'secs': 1.0, 'ok': True, 'errors': []}
    m.edge_check = lambda item, env, force: {'imports': {}, 'false': [], 'restore': {}, 'file': 'f'}
    assert m.scope(['piece'], {'piece:Q'}) == {'piece:Q'}
    assert m.run_all(kinds=['piece'], only={'piece:Q'})
    assert seen == ['piece:Q']
    assert json.load(open(os.path.join(m.cfg['work'], 'false_edges.json')))['orphaned_statements'] == []
