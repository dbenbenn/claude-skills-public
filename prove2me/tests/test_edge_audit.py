"""edge_audit.py on a fake platform: INCORRECT and MISSING edges, read from the submitted source."""
import pytest

import edge_audit as E

CODE = '''import Theorems.Thm_N_dep
import Theorems.Thm_N_unused

theorem other' : True := trivial

theorem solution : True := by
  have := other'
  exact N.dep
'''


class Fake:
    def __init__(self):
        filler = [{'id': 'f%d' % i, 'theorem_id': 'ZZ', 'status': 'ACCEPTED'} for i in range(100)]
        self.pages = {1: filler, 2: [{'id': 's1', 'theorem_id': 'T', 'status': 'ACCEPTED'}]}

    def call(self, method, path, body=None):
        if path.startswith('/missions?'):
            return {'missions': [{'id': 'M1', 'name': 'Test mission'}] if 'offset=0' in path else []}
        if path.startswith('/theorems?mission_id='):
            return {'theorems': [{'id': 'T', 'theorem_name': 'N.target', 'status': 'Proved',
                                  'formal_statement': 'theorem target : True := by\n  sorry'}] if 'offset=0' in path else []}
        if path.startswith('/submissions?page='):
            return {'submissions': self.pages.get(int(path.split('=')[1]), []), 'total': 101}
        if path == '/submissions/s1':
            return {'deprecated_at': None}
        if path == '/submissions/s1/solution':
            return {'content': CODE}
        if path == '/theorems/T/graph':
            nodes = [{'node_type': 'theorem', 'theorem_id': i, 'theorem_name': n}
                     for i, n in (('T', 'N.target'), ('D', 'N.dep'), ('U', 'N.unused'))]
            edges = [{'source': 'D', 'target': 'sketch-s1'}, {'source': 'U', 'target': 'sketch-s1'},
                     {'source': 'sketch-s1', 'target': 'T'}]
            return {'root_id': 'T', 'nodes': nodes, 'edges': edges}
        if path.startswith('/theorems?theorem_name='):
            return {'theorems': [{'theorem_name': path.split('=')[1], 'deprecated_at': None}]}
        raise AssertionError(path)


@pytest.fixture
def ws(tmp_path, monkeypatch):
    t = tmp_path / 'Theorems'
    t.mkdir()
    for n in ('dep', 'unused', 'other', 'target'):
        (t / ('Thm_N_%s.lean' % n)).write_text('namespace N\n\ntheorem %s : True := by\n  sorry\n\nend N\n' % n)
    # two copies of the workspace lookup (edge_audit's and prune_solution's): Phase 3 makes one
    import prune_solution
    monkeypatch.setattr(E, '_workspace', lambda: str(tmp_path))
    monkeypatch.setattr(prune_solution, '_workspace', lambda: str(tmp_path))
    return tmp_path


def test_incorrect_and_missing_edges_found_on_second_page(ws, monkeypatch, capsys):
    monkeypatch.setattr(E, 'call', Fake().call)
    monkeypatch.setattr(E.sys, 'argv', ['edge_audit.py', 'M1'])
    with pytest.raises(SystemExit) as e:
        E.main()
    out = capsys.readouterr().out
    assert e.value.code == 1
    assert 'INCORRECT edges (imports the proof never uses): 1' in out and 'Theorems.Thm_N_unused' in out
    assert 'MISSING edges (copied published theorem the graph does not reach): 1' in out and 'N.other' in out
    assert 'submitted s1' in out                       # judged from the platform's copy of the source
    assert 'UNMATCHED live proofs (source not fetched, no local file; not checked): 0' in out
