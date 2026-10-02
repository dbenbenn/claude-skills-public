"""deprecate.py: retire superseded proofs without ever leaving the theorem unproved."""
import pytest

import deprecate as D


class FakePlatform:
    """A theorem is Proved while some non-deprecated submission on it is ACCEPTED (a sketch alone
    is not enough when its dependencies are open -- the case that once unproved a theorem)."""
    def __init__(self, subs):
        self.subs = {s['id']: dict(s, deprecated_at=s.get('deprecated_at')) for s in subs}
        self.patches = []

    def call(self, method, path, body=None):
        if path.startswith('/submissions/'):
            sid = path.split('/')[2]
            if method == 'PATCH':
                self.patches.append((sid, body))
                self.subs[sid]['deprecated_at'] = '2026-10-02' if body['deprecated'] else None
                return {}
            return dict(self.subs[sid])
        if path.startswith('/theorems/'):
            tid = path.split('/')[2]
            live = [s for s in self.subs.values() if s['theorem_id'] == tid and not s['deprecated_at']]
            return {'status': 'Proved' if any(s['status'] == 'ACCEPTED' for s in live) else 'Open'}
        raise AssertionError(path)


def sub(sid, status='ACCEPTED', tid='T', **kw):
    return dict(id=sid, status=status, theorem_id=tid, theorem_name='N.' + tid, created_at='2026-10-01T00:00:00', **kw)


def run(monkeypatch, plat, *args):
    monkeypatch.setattr(D, 'call', plat.call)
    monkeypatch.setattr(D.time, 'sleep', lambda s: None)
    monkeypatch.setattr(D.sys, 'argv', ['deprecate.py'] + list(args))
    D.main()


def test_dry_run_patches_nothing(monkeypatch):
    plat = FakePlatform([sub('k'), sub('o')])
    run(monkeypatch, plat, '--keep', 'k', 'o')
    assert plat.patches == []


def test_happy_path(monkeypatch):
    plat = FakePlatform([sub('k'), sub('o')])
    run(monkeypatch, plat, '--keep', 'k', 'o', '--go')
    assert plat.subs['o']['deprecated_at'] and not plat.subs['k']['deprecated_at']


def test_refuses_a_deprecated_or_rejected_keeper(monkeypatch):
    for k in (sub('k', deprecated_at='x'), sub('k', status='WA')):
        with pytest.raises(SystemExit):
            run(monkeypatch, FakePlatform([k, sub('o')]), '--keep', 'k', 'o', '--go')


def test_refuses_a_proof_of_another_theorem(monkeypatch):
    plat = FakePlatform([sub('k'), sub('o', tid='U')])
    with pytest.raises(SystemExit):
        run(monkeypatch, plat, '--keep', 'k', 'o', '--go')
    assert plat.patches == []


def test_skips_an_already_deprecated_proof(monkeypatch):
    plat = FakePlatform([sub('k'), sub('o', deprecated_at='earlier')])
    run(monkeypatch, plat, '--keep', 'k', 'o', '--go')
    assert plat.patches == []


def test_undoes_a_deprecation_that_unproves_the_theorem(monkeypatch):
    # keeping only a sketch whose dependencies are open must not unprove the theorem
    plat = FakePlatform([sub('k', status='SKETCH_ACCEPTED'), sub('o')])
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, plat, '--keep', 'k', 'o', '--go')
    assert 'undone' in str(e.value)
    assert not plat.subs['o']['deprecated_at']
