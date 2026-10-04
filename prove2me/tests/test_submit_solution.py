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


def proof(sid='old', status='ACCEPTED', edges=True, content='-- an earlier proof\n', deprecated_at=None):
    return dict(id=sid, status=status, edges=edges, content=content, deprecated_at=deprecated_at,
                username='someone', explanation='We prove it by induction.')


def fake_platform(live_edges=None, live=None):
    """The theorem N.target (id T) with the live proofs `live` (default: one ACCEPTED proof, with the
    edge N.dep if live_edges). Like the platform, the graph has a sketch node only for a proof with
    theorem edges, and none for a deprecated one; /submissions lists them all."""
    if live is None:
        live = [proof(edges=bool(live_edges))] if live_edges is not None else []

    def call(method, path, body=None):
        if path.startswith('/theorems?theorem_name='):
            return {'theorems': [{'theorem_name': 'N.target', 'id': 'T'}]}
        if path == '/theorems/T/graph':
            nodes = [{'node_type': 'theorem', 'theorem_id': 'D', 'theorem_name': 'N.dep'}]
            edges = []
            for p in live:
                if p['edges'] and not p['deprecated_at']:
                    nodes.append({'node_type': 'sketch', 'submission_id': p['id'], 'parent_theorem_id': 'T',
                                  'status': p['status'], 'deprecated_at': None})
                    edges.append({'source': 'D', 'target': 'sketch-' + p['id']})
            return {'nodes': nodes, 'edges': edges}
        if path.startswith('/theorems/T/submissions?'):
            return {'submissions': [{k: v for k, v in p.items() if k not in ('edges', 'content')} for p in live],
                    'total': len(live)}
        for p in live:
            if path == '/submissions/%s/solution' % p['id']:
                return {'content': p['content']}
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
    # 000c8f8: Chornyi Cor 3 was resubmitted verbatim and its graph edges doubled. A note cannot
    # excuse the same source
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live=[proof(content=TOP + '\n')]), 'N.target', sol(tmp_path, TOP),
            '--explanation', expl(tmp_path), '--differs', note(tmp_path, 'old'), '--go')
    assert 'DUPLICATE' in str(e.value)


def test_same_edges_as_a_live_proof_is_already_proved(ws, tmp_path, monkeypatch):
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live_edges=True), 'N.target', sol(tmp_path, TOP), '--explanation', expl(tmp_path), '--go')
    assert 'ALREADY-PROVED' in str(e.value) and 'old' in str(e.value)


def test_replaces_lets_the_same_edges_through(ws, tmp_path, monkeypatch, capsys):
    run(monkeypatch, fake_platform(live_edges=True), 'N.target', sol(tmp_path, TOP), '--replaces', 'old')
    assert 'dry run' in capsys.readouterr().out


FULL = 'theorem solution : True := trivial\n'


def note(tmp_path, *sids, verdict='Different from'):
    p = tmp_path / 'comparison.md'
    p.write_text('%s %s: this proof argues by monotonicity of the action rather than by computing '
                 'the fixed points of each generator; the two share no lemma beyond the definitions.'
                 % (verdict, ' and '.join(sids)))
    return str(p)


def test_two_full_proofs_are_compared(ws, tmp_path, monkeypatch):
    # 2026-10-04: the graph has no sketch node for a full proof, so the duplicate check never saw
    # one; Lodha-Moore has two full proofs of one theorem, a different user's 11 minutes after ours
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live_edges=False), 'N.target', sol(tmp_path, FULL),
            '--explanation', expl(tmp_path), '--go')
    assert 'ALREADY-PROVED' in str(e.value)
    # dbenbenn: "you might have to go read the other proof to make a decision about whether it's
    # different" -- so the refusal saves it, Lean and explanation, beside ours
    assert (tmp_path / 'others' / 'Sol.old.lean').read_text() == '-- an earlier proof\n'
    assert 'induction' in (tmp_path / 'others' / 'Sol.old.md').read_text()
    assert 'others/Sol.old.lean' in str(e.value)


def test_a_proof_adding_edges_goes_through(ws, tmp_path, monkeypatch, capsys):
    # Lodha-Moore torsion-free: a 252-line direct proof was live; ours is the paper's route, with two
    # milestones as edges, which the graph had not recorded
    run(monkeypatch, fake_platform(live_edges=False), 'N.target', sol(tmp_path, TOP))
    out = capsys.readouterr().out
    assert 'dry run' in out and 'already proved' in out and 'N.dep' in out


def test_a_note_naming_the_proof_lets_it_through(ws, tmp_path, monkeypatch, capsys):
    run(monkeypatch, fake_platform(live_edges=False), 'N.target', sol(tmp_path, FULL), '--differs', note(tmp_path, 'old'))
    assert 'dry run' in capsys.readouterr().out


def test_a_same_as_note_is_no_excuse(ws, tmp_path, monkeypatch):
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live_edges=False), 'N.target', sol(tmp_path, FULL),
            '--differs', note(tmp_path, 'old', verdict='Same as'))
    assert 'ALREADY-PROVED' in str(e.value) and 'Different from' in str(e.value)


def test_a_note_not_naming_the_proof_is_refused(ws, tmp_path, monkeypatch):
    with pytest.raises(SystemExit) as e:
        run(monkeypatch, fake_platform(live_edges=False), 'N.target', sol(tmp_path, FULL),
            '--differs', note(tmp_path, 'another'))
    assert 'ALREADY-PROVED' in str(e.value) and 'does not name old' in str(e.value)


def test_an_unproved_theorem_takes_a_proof_with_fewer_edges(ws, tmp_path, monkeypatch, capsys):
    # a reduction whose child is still open does not prove the theorem; a full proof does
    run(monkeypatch, fake_platform(live=[proof(status='SKETCH_ACCEPTED')]), 'N.target', sol(tmp_path, FULL))
    assert 'dry run' in capsys.readouterr().out


def test_a_deprecated_proof_does_not_count(ws, tmp_path, monkeypatch, capsys):
    run(monkeypatch, fake_platform(live=[proof(edges=False, deprecated_at='2026-10-04T07:37:34Z')]),
        'N.target', sol(tmp_path, FULL))
    assert 'dry run' in capsys.readouterr().out


def test_blocking_unit():
    full, red = proof('f', edges=set()), proof('r', edges={'N.a', 'N.b'}, content='-- a reduction\n')
    assert S.blocking(set(), 'x', [full]) == ('ALREADY-PROVED', [full])
    assert S.blocking({'N.a'}, 'x', [full, red]) == ('ALREADY-PROVED', [red])    # inside red's edges
    assert S.blocking({'N.a', 'N.c'}, 'x', [full, red]) == (None, [])            # N.c is new
    assert S.blocking(set(), full['content'] + '\n\n', [full, red]) == ('DUPLICATE', [full])


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
