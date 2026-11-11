"""deprecate_run.py: retire everything one carve run published (its bundles and statements)."""
import json

import pytest

import deprecate_run as D


class FakePlatform:
    def __init__(self, deprecated=(), nested=False):
        self.dep = set(deprecated)
        self.nested = nested
        self.patches = []

    def call(self, method, path, body=None):
        assert path.startswith('/theorems/'), path
        tid = path.split('/')[2]
        if method == 'PATCH':
            self.patches.append((tid, body))
            self.dep.add(tid)
            return {}
        t = {'id': tid, 'deprecated_at': '2026-11-11' if tid in self.dep else None}
        return {'theorem': t} if self.nested else t


def state(tmp_path):
    s = {
        'bundle:Q1': {'id': 'b1', 'state': 'live'},
        'bundle:Q2': {'id': 'b2', 'state': 'stopped'},          # never went live: nothing to retire
        'statement:A': {'id': 's1', 'name': 'A_x', 'state': 'live'},
        'statement:B': {'id': 's2', 'name': 'B_x', 'state': 'live'},
        'piece:A': {'id': 's1', 'state': 'live'},               # a piece's id is its statement's theorem
        'piece:GOAL': {'id': 'g', 'state': 'stopped'},          # the goal piece: never a run's own theorem
    }
    p = tmp_path / 'run_state.json'
    p.write_text(json.dumps(s))
    r = tmp_path / 'reason.md'
    r.write_text('Built against the wrong definitions bundle; replaced by Q238L.\n')
    return str(p), str(r)


def run(monkeypatch, plat, *args):
    monkeypatch.setattr(D, 'call', plat.call)
    monkeypatch.setattr(D.time, 'sleep', lambda s: None)
    return D.main(list(args))


def test_dry_run_patches_nothing(monkeypatch, tmp_path):
    rs, reason = state(tmp_path)
    plat = FakePlatform()
    assert run(monkeypatch, plat, rs, '--reason', reason) == 0
    assert plat.patches == []


def test_deprecates_live_bundles_and_statements_only(monkeypatch, tmp_path):
    rs, reason = state(tmp_path)
    plat = FakePlatform()
    assert run(monkeypatch, plat, rs, '--reason', reason, '--go') == 0
    assert sorted(t for t, _ in plat.patches) == ['b1', 's1', 's2']
    assert all(b == {'deprecated': True, 'reason': 'Built against the wrong definitions bundle; replaced by Q238L.'}
               for _, b in plat.patches)


def test_skips_already_deprecated(monkeypatch, tmp_path):
    rs, reason = state(tmp_path)
    plat = FakePlatform(deprecated={'s1'}, nested=True)
    run(monkeypatch, plat, rs, '--reason', reason, '--go')
    assert sorted(t for t, _ in plat.patches) == ['b1', 's2']


def test_keep_id_refuses_whole_run(monkeypatch, tmp_path):
    rs, reason = state(tmp_path)
    plat = FakePlatform()
    with pytest.raises(SystemExit):
        run(monkeypatch, plat, rs, '--reason', reason, '--keep-id', 's2', '--go')
    assert plat.patches == []


def test_empty_reason_refused(monkeypatch, tmp_path):
    rs, reason = state(tmp_path)
    open(reason, 'w').write('  \n')
    with pytest.raises(SystemExit):
        run(monkeypatch, FakePlatform(), rs, '--reason', reason, '--go')
