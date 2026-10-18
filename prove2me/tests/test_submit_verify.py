"""submit_verify.post_verify: it refuses a theorem that already has a live proof unless told why.

2026-10-18: a bridge proof of Erdos3.erdos_3 was sent by calling post_verify directly, beside a
line-for-line identical reduction accepted ten days earlier (submit_solution.py would have
refused it, but was not used). The guard sits in post_verify so no caller can skip it."""
import io
import json
import urllib.request

import pytest

import submit_verify
from p2mlib import api

REAL_POST = submit_verify.post_verify      # taken before the autouse fixture replaces it

ROWS = [
    {'id': 'old-accepted', 'status': 'ACCEPTED', 'created_at': '2026-10-08T11:24', 'username': 'dbenbenn',
     'deprecated_at': None},
    {'id': 'gone', 'status': 'ACCEPTED', 'created_at': '2026-10-01T00:00', 'username': 'x',
     'deprecated_at': '2026-10-02T00:00'},
    {'id': 'rejected', 'status': 'WA', 'created_at': '2026-10-09T00:00', 'username': 'dbenbenn',
     'deprecated_at': None},
]


def fake_call(rows):
    seen = []

    def call(method, path, body=None):
        seen.append((method, path))
        assert method == 'GET' and path.startswith('/theorems/T/submissions'), path
        return {'submissions': rows, 'total': len(rows)}
    call.seen = seen
    return call


@pytest.fixture
def no_post(monkeypatch):
    def refuse(*a, **k):
        raise AssertionError('POST /verify was reached')
    monkeypatch.setattr(urllib.request, 'urlopen', refuse)
    monkeypatch.setattr(submit_verify, 'token', lambda refresh=False: 'tok')


@pytest.fixture
def sol(tmp_path):
    p = tmp_path / 'Sol.lean'
    p.write_text('theorem solution : True := trivial\n')
    return str(p)


def test_live_proofs_keeps_live_accepted_sketches_and_pending():
    rows = ROWS + [{'id': 'sk', 'status': 'SKETCH_ACCEPTED', 'deprecated_at': None},
                   {'id': 'p', 'status': 'PENDING', 'deprecated_at': None}]
    assert [r['id'] for r in api.live_proofs('T', call=fake_call(rows))] == ['old-accepted', 'sk', 'p']


def test_refuses_a_proved_theorem_and_names_the_proof(monkeypatch, no_post, sol):
    monkeypatch.setattr(submit_verify, 'call', fake_call(ROWS))
    with pytest.raises(submit_verify.ExistingProof) as e:
        REAL_POST('T', sol, 'expl')
    msg = str(e.value)
    assert 'old-accepted' in msg and 'ACCEPTED' in msg and '2026-10-08' in msg and 'dbenbenn' in msg
    assert 'also=' in msg and 'submit_solution.py' in msg


def test_refusal_is_a_runtime_error_so_the_split_runner_stops_only_that_item(monkeypatch, no_post, sol):
    monkeypatch.setattr(submit_verify, 'call', fake_call(ROWS))
    with pytest.raises(RuntimeError):
        REAL_POST('T', sol)


def test_no_live_proof_posts(monkeypatch, sol):
    monkeypatch.setattr(submit_verify, 'call', fake_call([r for r in ROWS if r['id'] != 'old-accepted']))
    monkeypatch.setattr(submit_verify, 'token', lambda refresh=False: 'tok')
    sent = []

    class Resp(io.BytesIO):
        def __enter__(self): return self
        def __exit__(self, *a): pass

    def urlopen(req, timeout=None):
        sent.append(req)
        return Resp(json.dumps({'submission_id': 'new'}).encode())
    monkeypatch.setattr(urllib.request, 'urlopen', urlopen)
    assert REAL_POST('T', sol)['submission_id'] == 'new'
    assert len(sent) == 1


def test_a_stated_reason_or_a_prior_check_lets_it_through(monkeypatch, sol):
    monkeypatch.setattr(submit_verify, 'call', fake_call(ROWS))
    monkeypatch.setattr(submit_verify, 'token', lambda refresh=False: 'tok')

    class Resp(io.BytesIO):
        def __enter__(self): return self
        def __exit__(self, *a): pass
    monkeypatch.setattr(urllib.request, 'urlopen', lambda req, timeout=None: Resp(b'{"submission_id": "s"}'))
    assert REAL_POST('T', sol, also='replaces a sketch whose dependency is stuck')['submission_id'] == 's'
    assert REAL_POST('T', sol, checked=True)['submission_id'] == 's'


def test_empty_reason_does_not_count(monkeypatch, no_post, sol):
    monkeypatch.setattr(submit_verify, 'call', fake_call(ROWS))
    with pytest.raises(submit_verify.ExistingProof):
        REAL_POST('T', sol, also='  ')


def test_cli_parses_also_with_its_reason():
    assert submit_verify.parse_args(['T', 'S.lean', 'E.md', '--also', 'other mathematics']) == \
        ('T', 'S.lean', 'E.md', None, 'other mathematics')
    assert submit_verify.parse_args(['--disprove', 'T', 'S.lean']) == ('T', 'S.lean', None, 'disprove', None)
    with pytest.raises(SystemExit):
        submit_verify.parse_args(['T', 'S.lean', '--also'])           # a reason is required
    with pytest.raises(SystemExit):
        submit_verify.parse_args(['T', 'S.lean', '--disproof'])       # a mistyped flag still refuses
