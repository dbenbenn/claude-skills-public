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
    for n in 'abc':
        (m / 'solutions' / ('Sol_%s.lean' % n)).write_text('theorem solution : True := trivial\n')
        (ws / ('Thm_TestNS_%s.lean' % n)).write_text('')
    (m / 'solutions' / 'submitted.json').write_text(json.dumps({n: 'held' for n in 'abc'}))
    monkeypatch.setattr(S, '_workspace', lambda: str(tmp_path / 'ws'))
    monkeypatch.setattr(S.subprocess, 'run', lambda *a, **k: types.SimpleNamespace(returncode=0, stdout='', stderr=''))
    return m


def run(m, monkeypatch, submit, call=lambda *a, **k: {}):
    monkeypatch.setattr(S, 'submit', submit)
    monkeypatch.setattr(S, 'call', call)
    monkeypatch.setattr(S.sys, 'argv', ['submit_all.py', str(m), '--proposal', 'x', '--check', 'X', '--every', '0'])
    with pytest.raises(SystemExit) as e:
        S.main()
    return e.value.code, json.loads((m / 'solutions' / 'submitted.json').read_text())


def test_retry_then_accept_and_pending_polled_not_resubmitted(mission, monkeypatch):
    n_sub = {'b': 0, 'c': 0}

    def submit(ns, n, f):
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

    def submit(ns, n, f):
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

    def submit(ns, n, f):
        when[n] = rounds[0]
        return 'ACCEPTED s-' + n
    code, done = run(mission, monkeypatch, submit)
    assert code == 0 and all(v.startswith('ACCEPTED') for v in done.values())
    assert when['a'] == 1 and when['c'] == 1 and when['b'] == 2
