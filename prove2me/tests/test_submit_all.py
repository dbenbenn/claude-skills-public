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
