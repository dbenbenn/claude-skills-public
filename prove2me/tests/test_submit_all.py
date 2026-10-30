"""submit_all: parallel submission, retries, late verdicts, final attention list (f14bd2d)."""
import json
import types

import pytest

import submit_all as S


@pytest.fixture
def mission(tmp_path, monkeypatch):
    m = tmp_path / 'm'
    (m / 'solutions').mkdir(parents=True)
    (m / 'mission.py').write_text("NAMESPACE='TestNS'\nTHEOREMS=[dict(name='a'),dict(name='b'),dict(name='c')]\n")
    ws = tmp_path / 'ws' / 'Theorems'
    ws.mkdir(parents=True)
    (m / 'explanations').mkdir()
    for n in 'abc':
        (m / 'solutions' / ('Sol_%s.lean' % n)).write_text('theorem solution : True := trivial\n')
        (ws / ('Thm_TestNS_%s.lean' % n)).write_text('')
        (m / 'explanations' / ('%s.md' % n)).write_text('We prove $$\\mathrm{True}.$$ ' + 'x' * 200)
    (m / 'solutions' / 'submitted.json').write_text(json.dumps({n: 'held' for n in 'abc'}))
    monkeypatch.setattr(S, '_workspace', lambda: str(tmp_path / 'ws'))
    monkeypatch.setattr(S.subprocess, 'run', lambda *a, **k: types.SimpleNamespace(returncode=0, stdout='', stderr=''))
    return m


def run(m, monkeypatch, submit, call=lambda *a, **k: {}, proposal=('--proposal', 'x')):
    monkeypatch.setattr(S, 'submit', submit)
    monkeypatch.setattr(S, 'call', call)
    monkeypatch.setattr(S.sys, 'argv', ['submit_all.py', str(m), *proposal, '--check', 'X', '--every', '0'])
    with pytest.raises(SystemExit) as e:
        S.main()
    return e.value.code, json.loads((m / 'solutions' / 'submitted.json').read_text())


def test_without_a_proposal_fetches_the_folders_statements_by_name(mission, monkeypatch):
    # Erschler-Zheng 2026-10-06: a standalone package has no proposal; its statements publish one by
    # one through publish_standalone.py, and each proof should go in as its statement publishes
    (mission / 'mission.py').write_text("NAMESPACE='TestNS'\nTHEOREMS=[dict(name='a'),dict(name='b'),"
                                        "dict(name='c', namespace='Ext')]\n")
    (mission / 'solutions' / 'submitted.json').write_text(json.dumps({'a': 'held', 'b': 'held'}))
    fetched = []

    def fake_run(cmd, *a, **k):
        if any('fetch_theorems.py' in str(c) for c in cmd):
            fetched.append(cmd[cmd.index(next(c for c in cmd if 'fetch_theorems.py' in str(c))) + 1:])
            (mission.parent / 'ws' / 'Theorems' / 'Thm_Ext_c.lean').write_text('')
        return types.SimpleNamespace(returncode=0, stdout='OK', stderr='')
    monkeypatch.setattr(S.subprocess, 'run', fake_run)
    code, done = run(mission, monkeypatch, lambda ns, n, f, expl=None, differs=None: 'ACCEPTED s-' + n,
                     proposal=())
    assert code == 0 and done['c'] == 'ACCEPTED s-c'
    assert fetched[0] == ['--names', 'TestNS.a', 'TestNS.b', 'Ext.c']


def test_retry_then_accept_and_pending_polled_not_resubmitted(mission, monkeypatch):
    n_sub = {'b': 0, 'c': 0}

    def submit(ns, n, f, expl=None, differs=None):
        if n == 'a':
            return 'ACCEPTED s1'
        n_sub[n] += 1
        if n == 'b':
            return 'WA s2' if n_sub['b'] == 1 else 'ACCEPTED s3'
        return 'PENDING s4'
    code, done = run(mission, monkeypatch, submit,
                     call=lambda m, p, b=None: {'status': 'ACCEPTED'} if p == '/submissions/s4' else {})
    assert code == 0
    assert done == {'a': 'ACCEPTED s1', 'b': 'ACCEPTED s3', 'c': 'ACCEPTED s4'}
    assert n_sub == {'b': 2, 'c': 1}          # c's late verdict was polled, never resubmitted


def test_failed_after_retries_and_duplicate_not_retried(mission, monkeypatch):
    calls = []

    def submit(ns, n, f, expl=None, differs=None):
        calls.append(n)
        return {'a': 'ACCEPTED s1', 'b': 'WA sX', 'c': 'DUPLICATE: live submission y'}[n]
    code, done = run(mission, monkeypatch, submit)
    assert code == 1
    assert done['b'] == 'FAILED WA sX (after 3 tries)' and calls.count('b') == 3
    assert done['c'].startswith('DUPLICATE') and calls.count('c') == 1


def test_a_draft_stub_is_not_published(tmp_path):
    # Lodha-Moore 2026-10-02: the stubs made every statement look published, and five solutions were
    # sent while the publish queue had not reached them
    import submit_all as S
    from p2mlib.workspace import set_drafts
    (tmp_path / 'Theorems').mkdir()
    for n in ('a', 'b'):
        (tmp_path / 'Theorems' / ('Thm_N_%s.lean' % n)).write_text('theorem N.%s : True := by sorry\n' % n)
    set_drafts({'Theorems.Thm_N_b': '/m'}, str(tmp_path))
    assert S.published_names(['a', 'b', 'c'], 'N', str(tmp_path)) == ['a']


def test_an_entry_in_its_own_namespace(mission, monkeypatch, tmp_path):
    # Erschler-Zheng 2026-10-06: the external entries (namespace KaimanovichVershik, Bartholdi) were
    # looked up as Thm_<NAMESPACE>_<name>, so they never counted as published and were never submitted
    (mission / 'mission.py').write_text("NAMESPACE='TestNS'\nTHEOREMS=[dict(name='a'),dict(name='b'),"
                                        "dict(name='c', namespace='Ext.Sub')]\n")
    ws = tmp_path / 'ws' / 'Theorems'
    (ws / 'Thm_TestNS_c.lean').unlink()
    (ws / 'Thm_Ext_Sub_c.lean').write_text('')
    rounds = [0]

    def fake_run(cmd, *a, **k):
        if any('fetch_theorems.py' in str(c) for c in cmd):
            rounds[0] += 1
            if rounds[0] > 3:
                raise RuntimeError('c was never taken for published')
        return types.SimpleNamespace(returncode=0, stdout='', stderr='')
    monkeypatch.setattr(S.subprocess, 'run', fake_run)
    got = {}

    def submit(ns, n, f, expl=None, differs=None):
        got[n] = ns
        return 'ACCEPTED s-' + n
    code, done = run(mission, monkeypatch, submit)
    assert code == 0 and done['c'] == 'ACCEPTED s-c'
    assert got == {'a': 'TestNS', 'b': 'TestNS', 'c': 'Ext.Sub'}


def test_waits_while_an_import_is_unpublished(mission, monkeypatch, tmp_path):
    # CFW 2026-10-03: proofs import sibling stubs; a solution importing a statement the publish
    # queue has not reached was REFUSED by submit_solution, and REFUSED is recorded as final
    from p2mlib.workspace import set_drafts
    ws = tmp_path / 'ws'
    (ws / 'Theorems' / 'Thm_Other_x.lean').write_text('theorem Other.x : True := by sorry\n')
    set_drafts({'Theorems.Thm_Other_x': '/m'}, str(ws))
    (mission / 'solutions' / 'Sol_b.lean').write_text('import Theorems.Thm_Other_x\ntheorem solution : True := trivial\n')
    rounds = [0]

    def fake_run(cmd, *a, **k):
        if any('fetch_theorems.py' in str(c) for c in cmd):
            rounds[0] += 1
            if rounds[0] == 2:          # the queue publishes Other.x: fetch retires the stub
                set_drafts({}, str(ws))
        return types.SimpleNamespace(returncode=0, stdout='', stderr='')
    monkeypatch.setattr(S.subprocess, 'run', fake_run)
    when = {}

    def submit(ns, n, f, expl=None, differs=None):
        when[n] = rounds[0]
        return 'ACCEPTED s-' + n
    code, done = run(mission, monkeypatch, submit)
    assert code == 0 and all(v.startswith('ACCEPTED') for v in done.values())
    assert when['a'] == 1 and when['c'] == 1 and when['b'] == 2


def test_waits_for_its_explanation_and_passes_it(mission, monkeypatch):
    # 2026-10-04: 480 of 1053 accepted submissions had no explanation; a proof is submitted only
    # with MISSION_DIR/explanations/<name>.md, and waits (unrecorded) until that file exists
    (mission / 'explanations' / 'b.md').unlink()
    rounds = [0]

    def fake_run(cmd, *a, **k):
        if any('fetch_theorems.py' in str(c) for c in cmd):
            rounds[0] += 1
            if rounds[0] == 2:
                (mission / 'explanations' / 'b.md').write_text('We prove $$\\mathrm{True}.$$ ' + 'x' * 200)
        return types.SimpleNamespace(returncode=0, stdout='', stderr='')
    monkeypatch.setattr(S.subprocess, 'run', fake_run)
    when, got = {}, {}

    def submit(ns, n, f, expl=None, differs=None):
        when[n], got[n] = rounds[0], expl
        return 'ACCEPTED s-' + n
    code, done = run(mission, monkeypatch, submit)
    assert code == 0 and all(v.startswith('ACCEPTED') for v in done.values())
    assert when['a'] == 1 and when['b'] == 2
    assert got['b'].endswith('explanations/b.md')


def test_already_proved_waits_for_a_comparison(mission, monkeypatch):
    # dbenbenn 2026-10-04: when the theorem got proved meanwhile, submit ours only if it is
    # meaningfully different, which means reading the other proof; comparisons/<name>.md records
    # the reading: "Different from <id>: ..." submits it, "Same as <id>: ..." settles the skip
    got = {}

    def submit(ns, n, f, expl=None, differs=None):
        got[n] = differs
        if n in 'bc' and differs is None:
            return 'ALREADY-PROVED: 226ad5b4 (Nickrobbins95, ACCEPTED, edges none)'
        return 'ACCEPTED s-' + n
    code, done = run(mission, monkeypatch, submit)
    assert code == 0 and done['b'].startswith('ALREADY-PROVED') and done['c'].startswith('ALREADY-PROVED')
    (mission / 'comparisons').mkdir()
    (mission / 'comparisons' / 'b.md').write_text('Same as 226ad5b4: the same induction on word length.')
    (mission / 'comparisons' / 'c.md').write_text('Different from 226ad5b4: ...')
    got.clear()
    code, done = run(mission, monkeypatch, submit)
    assert code == 0 and done['c'] == 'ACCEPTED s-c' and got == {'c': str(mission / 'comparisons' / 'c.md')}
    assert done['b'].startswith('SKIPPED same as 226ad5b4')


def test_a_waiting_import_published_meanwhile_is_fetched_by_name(mission, monkeypatch, tmp_path):
    # oaiq-100 (2026-10-29): the import was a sibling of ANOTHER mission, published and proved, but
    # still a draft stub here: the round's own fetch (--proposal / this folder's names) never names
    # it, so the solution would wait for ever. The live API is asked, and `--names` fetches it.
    from p2mlib.workspace import set_drafts
    ws = tmp_path / 'ws'
    (ws / 'Theorems' / 'Thm_Other_x.lean').write_text('theorem Other.x : True := by sorry\n')
    set_drafts({'Theorems.Thm_Other_x': '/m'}, str(ws))
    (mission / 'solutions' / 'Sol_b.lean').write_text('import Theorems.Thm_Other_x\ntheorem solution : True := trivial\n')
    fetched = []

    def fake_run(cmd, *a, **k):
        if '--names' in cmd:
            fetched.append(cmd[cmd.index('--names') + 1:])
            set_drafts({}, str(ws))
        return types.SimpleNamespace(returncode=0, stdout='', stderr='')
    monkeypatch.setattr(S.subprocess, 'run', fake_run)

    def call(method, path, body=None):
        if path.startswith('/theorems?theorem_name=Other.x'):
            return {'theorems': [{'theorem_name': 'Other.x', 'id': 'X', 'status': 'Proved'}]}
        return {}
    code, done = run(mission, monkeypatch, lambda ns, n, f, expl=None, differs=None: 'ACCEPTED s-' + n, call=call)
    assert code == 0 and done['b'] == 'ACCEPTED s-b' and fetched == [['Other.x']]


def test_the_hold_message_names_the_fetch(mission, monkeypatch, tmp_path, capsys):
    from p2mlib.workspace import set_drafts
    ws = tmp_path / 'ws'
    (ws / 'Theorems' / 'Thm_Other_x.lean').write_text('theorem Other.x : True := by sorry\n')
    set_drafts({'Theorems.Thm_Other_x': '/m'}, str(ws))
    (mission / 'solutions' / 'Sol_b.lean').write_text('import Theorems.Thm_Other_x\ntheorem solution : True := trivial\n')
    rounds = [0]

    def fake_run(cmd, *a, **k):
        if '--proposal' in cmd:
            rounds[0] += 1
            if rounds[0] == 2:
                set_drafts({}, str(ws))
        return types.SimpleNamespace(returncode=0, stdout='', stderr='')
    monkeypatch.setattr(S.subprocess, 'run', fake_run)
    code, done = run(mission, monkeypatch, lambda ns, n, f, expl=None, differs=None: 'ACCEPTED s-' + n)
    assert code == 0 and done['b'] == 'ACCEPTED s-b'
    assert 'fetch_theorems.py --names Other.x' in capsys.readouterr().out


def test_a_disproved_import_refusal_is_final(monkeypatch):
    # oaiq-109: submit_all submits only through submit_solution.py, whose Disproved-import refusal
    # (p2mlib.importcheck) must be recorded as final, not retried
    out = 'REFUSED: imports Disproved theorems, so the target could never become Proved:\n  N.dep\n'
    seen = []

    def fake_run(cmd, *a, **k):
        seen.append(cmd)
        return types.SimpleNamespace(returncode=1, stdout='', stderr=out)
    monkeypatch.setattr(S.subprocess, 'run', fake_run)
    res = S.submit('N', 'target', 'Sol.lean', 'e.md')
    assert seen[0][1].endswith('submit_solution.py') and '--go' in seen[0]
    assert res.startswith(S.FINAL) and 'Disproved' in res
