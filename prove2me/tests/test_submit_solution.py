"""submit_solution.py: refusals before anything is sent, and honest verdict reporting."""
import types

import pytest

import submit_solution as S

TOP = 'import Theorems.Thm_N_dep\n\ntheorem solution : True := N.dep\n'


@pytest.fixture
def ws(tmp_path, monkeypatch):
    (tmp_path / 'Theorems').mkdir()
    (tmp_path / 'Theorems' / 'Thm_N_dep.lean').write_text('namespace N\n\ntheorem dep : True := by\n  sorry\n\nend N\n')
    monkeypatch.setattr(S, '_workspace', lambda: str(tmp_path))
    return tmp_path


def sol(tmp_path, text):
    p = tmp_path / 'Sol.lean'
    p.write_text(text)
    return str(p)


def test_solution_inside_namespace_refused(tmp_path):
    # measured 2026-09-26: the checker wants `solution` at top level (WA "Unknown identifier")
    with pytest.raises(SystemExit):
        S.check_solution_top_level(sol(tmp_path, 'namespace N\ntheorem solution : True := trivial\nend N\n'))
    S.check_solution_top_level(sol(tmp_path, 'open N in\ntheorem solution : True := trivial\n'))


def test_metaprogramming_refused(tmp_path):
    with pytest.raises(SystemExit):
        S.check_no_metaprogramming(sol(tmp_path, 'macro "x" : term => `(1)\ntheorem solution : True := trivial\n'))


def test_import_names_reads_the_declaration_not_a_docstring(ws, tmp_path):
    (ws / 'Theorems' / 'Thm_N_dep.lean').write_text(
        '/-! theorem for balls: a module docstring -/\nnamespace N\n\ntheorem dep : True := by\n  sorry\n\nend N\n')
    assert S.import_names(sol(tmp_path, TOP)) == {'N.dep'}


def fake_platform(live_edges, verdict='ACCEPTED'):
    def call(method, path, body=None):
        if path.startswith('/theorems?theorem_name='):
            return {'theorems': [{'theorem_name': 'N.target', 'id': 'T'}]}
        if path == '/theorems/T/graph':
            nodes = [{'node_type': 'theorem', 'theorem_id': 'D', 'theorem_name': 'N.dep'},
                     {'node_type': 'sketch', 'submission_id': 'old', 'parent_theorem_id': 'T',
                      'status': 'ACCEPTED', 'deprecated_at': None}]
            edges = [{'source': 'D', 'target': 'sketch-old'}] if live_edges else []
            return {'nodes': nodes, 'edges': edges}
        raise AssertionError(path)
    return call


EXPL = 'We prove $$\\mathrm{True}.$$ It follows from the imported statement, applied once. ' + 'x' * 150


def expl(tmp_path, text=EXPL):
    p = tmp_path / 'expl.md'
    p.write_text(text)
    return str(p)


def run(monkeypatch, call, *args):
    monkeypatch.setattr(S, 'call', call)
    monkeypatch.setattr(S, 'check_no_inline_copies', lambda *a: None)
    monkeypatch.setattr(S.sys, 'argv', ['submit_solution.py'] + list(args))
    return S.main()


def test_duplicate_of_a_live_proof_refused(ws, tmp_path, monkeypatch):
    # 000c8f8: Chornyi Cor 3 was resubmitted verbatim and its graph edges doubled
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live_edges=True), 'N.target', sol(tmp_path, TOP), '--explanation', expl(tmp_path), '--go')
    assert 'DUPLICATE' in str(e.value)


def test_replaces_lets_the_same_edges_through(ws, tmp_path, monkeypatch, capsys):
    run(monkeypatch, fake_platform(live_edges=True), 'N.target', sol(tmp_path, TOP), '--replaces', 'old')
    assert 'dry run' in capsys.readouterr().out


def test_late_verdict_is_pending_not_rejected(ws, tmp_path, monkeypatch):
    # 7da9719: a 21-minute compile was reported as "not accepted: None"; it was ACCEPTED
    import submit_verify
    monkeypatch.setattr(submit_verify, 'post_verify', lambda *a: {'submission_id': 'new'})
    monkeypatch.setattr(submit_verify, 'poll', lambda sid: {'status': 'PENDING', '__error': 'no verdict after 60 minutes'})
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live_edges=False), 'N.target', sol(tmp_path, TOP), '--explanation', expl(tmp_path), '--go')
    assert 'PENDING' in str(e.value) and 'not accepted' not in str(e.value)


def test_go_without_an_explanation_is_refused(ws, tmp_path, monkeypatch):
    # 2026-10-04: 480 of 1053 accepted submissions had no explanation (prove.md asks for one)
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live_edges=False), 'N.target', sol(tmp_path, TOP), '--go')
    assert 'no --explanation' in str(e.value)


def test_an_explanation_without_the_statement_display_is_refused(ws, tmp_path, monkeypatch):
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live_edges=False), 'N.target', sol(tmp_path, TOP),
            '--explanation', expl(tmp_path, 'It follows from the imported statement. ' * 10), '--go')
    assert 'display' in str(e.value)
