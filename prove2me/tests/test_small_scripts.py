"""publish_status, watch_proposal and check_server_shape."""
import os
import shutil
import subprocess
import sys

import pytest

from conftest import SCRIPTS
from mini import make_mission


def test_publish_status_ignores_reference_jobs_and_lists_failures(monkeypatch):
    import publish_status as PS

    def call(m, p, b=None):
        if p == '/mission-proposals/P':
            return {'status': 'Draft', 'submitted_at': None, 'items': [
                {'kind': 'theorem', 'theorem_name': 'N.a'}, {'kind': 'theorem', 'theorem_name': 'N.b'},
                {'kind': 'reference', 'theorem_name': 'Other.old'}]}
        return {'publish_jobs': [
            {'theorem_name': 'N.a', 'status': 'PUBLISHED'},
            {'theorem_name': 'N.b', 'status': 'FAILED', 'error_message': 'unknown identifier'},
            {'theorem_name': 'Other.old', 'status': 'PUBLISHED'}]}     # a reference's old job (Moore, 2026-10-01)
    monkeypatch.setattr(PS, 'call', call)
    st, sub, n, by, failed = PS.snapshot('P')
    assert n == 2 and by == {'FAILED': 1, 'PUBLISHED': 1} and failed == [('N.b', 'unknown identifier')]
    monkeypatch.setattr(PS, 'call', lambda m, p, b=None: {'__error': '502'})
    assert PS.snapshot('P') is None                       # a failed fetch is retried, never fatal


def test_watch_proposal_exits_on_change(monkeypatch, capsys):
    import watch_proposal as W
    states = iter([('In review', None), ('In review', None), ('Approved', 'M1')])
    monkeypatch.setattr(W, 'state', lambda pid: next(states))
    monkeypatch.setattr(W.time, 'sleep', lambda s: None)
    monkeypatch.setattr(W.sys, 'argv', ['watch_proposal.py', 'abcdef12'])
    W.main()
    out = capsys.readouterr().out
    assert 'status In review' in out and 'CHANGED In review -> Approved mission M1' in out


@pytest.mark.lean
def test_check_server_shape_catches_a_missing_open(tmp_path):
    m = make_mission(tmp_path / 'srvshape_mission')
    (m / 'lib' / 'Thm_Mini.lean').write_text(
        'open MulOpposite\n\nnamespace Mini\n\ntheorem t1 : (op (1 : ℕ)).unop = 1 := by\n  sorry\n\n'
        'theorem goal : 1 + 1 = 2 := by\n  sorry\n\nend Mini\n')
    from prune_solution import _workspace
    srv = os.path.join(_workspace(), 'Solutions', '_srv', 'srvshape_mission')
    try:
        r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'check_server_shape.py'), str(m)],
                           capture_output=True, text=True, timeout=1800)
    finally:
        shutil.rmtree(srv, ignore_errors=True)
    assert 'FAIL t1' in r.stdout and 'OK   goal' in r.stdout and r.returncode != 0
