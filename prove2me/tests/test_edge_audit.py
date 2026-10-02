"""edge_audit.py: INCORRECT, MISSING and SHARED, judged by Lean on the submitted source.

Offline: judge/report and the live flow on a fake platform, with the analysis of
lean_fixtures/Audit.lean replayed from its recording. With P2M_LEAN=1: the analysis itself."""
import json
import os

import pytest

import edge_audit as E
from p2mlib import leaninfo as LI
from p2mlib.workspace import Published

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures')
CODE = open(os.path.join(FIX, 'Audit.lean')).read()
BYFULL = {f: Published(f, 'Theorems.Thm_' + f.replace('.', '_'), [])
          for f in ('BlockCycleRotation.fib_two_le', 'BlockCycleRotation.gcd_min_eq',
                    'HomeoLine.zpow_moves_of_moves', 'N.target', 'N.other')}
SAME = {'Dev.moves': ['HomeoLine.zpow_moves_of_moves']}


def recorded():
    return LI.parse(json.load(open(os.path.join(FIX, 'Audit.json'))), CODE.encode())


def test_judge_incorrect_missing_and_top():
    inc, mis, top = E.judge(recorded(), SAME, 'N.target', {'BlockCycleRotation.fib_two_le'}, BYFULL,
                            lambda f: False)
    assert inc == ['Theorems.Thm_BlockCycleRotation_gcd_min_eq']      # imported, never used
    assert mis == [('Dev.moves', 'HomeoLine.zpow_moves_of_moves', 'statement')]
    assert top == {'moves'}                                            # unused_helper is pruned away


def test_reached_or_deprecated_copies_are_not_missing():
    info = recorded()
    _, mis, _ = E.judge(info, SAME, 'N.target', {'HomeoLine.zpow_moves_of_moves'}, BYFULL, lambda f: False)
    assert mis == []
    _, mis, _ = E.judge(info, SAME, 'N.target', set(), BYFULL, lambda f: True)
    assert mis == []


class Fake:
    def __init__(self):
        filler = [{'id': 'f%d' % i, 'theorem_id': 'ZZ', 'status': 'ACCEPTED'} for i in range(100)]
        self.pages = {1: filler, 2: [{'id': 's1', 'theorem_id': 'T', 'status': 'ACCEPTED'}]}

    def call(self, method, path, body=None):
        if path.startswith('/missions?'):
            return {'missions': [{'id': 'M1', 'name': 'Test mission'}] if 'offset=0' in path else []}
        if path.startswith('/theorems?mission_id='):
            return {'theorems': [{'id': 'T', 'theorem_name': 'N.target', 'status': 'Proved'}] if 'offset=0' in path else []}
        if path.startswith('/submissions?page='):
            return {'submissions': self.pages.get(int(path.split('=')[1]), []), 'total': 101}
        if path == '/submissions/s1':
            return {'deprecated_at': None}
        if path == '/submissions/s1/solution':
            return {'content': CODE}
        if path == '/theorems/T/graph':
            nodes = [{'node_type': 'theorem', 'theorem_id': i, 'theorem_name': n}
                     for i, n in (('T', 'N.target'), ('F', 'BlockCycleRotation.fib_two_le'),
                                  ('G', 'BlockCycleRotation.gcd_min_eq'))]
            edges = [{'source': 'F', 'target': 'sketch-s1'}, {'source': 'G', 'target': 'sketch-s1'},
                     {'source': 'sketch-s1', 'target': 'T'}]
            return {'root_id': 'T', 'nodes': nodes, 'edges': edges}
        if path.startswith('/theorems?theorem_name='):
            return {'theorems': [{'theorem_name': path.split('=')[1], 'deprecated_at': None}]}
        raise AssertionError(path)


def test_live_audit_on_second_page(monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(E, 'call', Fake().call)
    monkeypatch.setattr(E, 'CACHE', str(tmp_path))
    monkeypatch.setattr(E, 'published_by_full', lambda ws, with_drafts=False: BYFULL)
    seen = []
    monkeypatch.setattr(E, 'analyze', lambda path, ws, with_drafts=False: (seen.append(open(path).read()), (recorded(), SAME))[1])
    assert E.live(['M1'], str(tmp_path)) == 1
    out = capsys.readouterr().out
    assert seen == [CODE]                                   # judged from the platform's copy
    assert 'INCORRECT edges (imports the proof never uses): 1' in out and 'gcd_min_eq' in out
    assert 'MISSING edges' in out and 'Dev.moves <- HomeoLine.zpow_moves_of_moves  (by statement)' in out
    assert 'UNCHECKED proofs: 0' in out


def test_local_audit_treats_draft_siblings_as_published(monkeypatch, tmp_path, capsys):
    # LM, 2026-10-02: under the stubs flow a proof imports its siblings' draft stubs, and a sibling
    # it re-derives is unpublished too; before submitting, both are about to be graph nodes
    d = tmp_path / 'sol'
    d.mkdir()
    (d / 'Sol_target.lean').write_text('import Theorems.Thm_HomeoLine_zpow_moves_of_moves\n' + CODE)
    calls = []

    def byfull(ws, with_drafts=False):
        calls.append(('byfull', with_drafts))
        return BYFULL
    monkeypatch.setattr(E, 'published_by_full', byfull)
    monkeypatch.setattr(E, 'analyze', lambda path, ws, with_drafts=False:
                        (calls.append(('analyze', with_drafts)), (recorded(), SAME))[1])
    E.local(str(d), str(tmp_path))
    out = capsys.readouterr().out
    assert calls == [('byfull', True), ('analyze', True)]
    assert 'MISSING edges (a published theorem re-derived, not reached by the graph): 0' in out


def test_shared_top_steps_reported_between_unrelated_proofs(capsys):
    proofs = [('N.a', 's1', set()), ('N.b', 's2', set()), ('N.c', 's3', {'N.a'}), ('N.b', 's4', set())]
    results = [(None, ([], [], {'lemma1', 'basic'})), (None, ([], [], {'lemma1'})), (None, ([], [], {'lemma1'})),
               (None, ([], [], {'lemma1'}))]
    assert E.report(proofs, results) == 0
    out = capsys.readouterr().out
    assert 'N.a  and  N.b:  lemma1' in out and 'N.b  and  N.c:  lemma1' in out
    assert out.count('N.a  and  N.b:  lemma1') == 1          # N.b's second live proof: one line
    assert 'N.a  and  N.c' not in out                       # c reaches a


@pytest.mark.lean
def test_analysis_by_lean():
    info, same = E.analyze(os.path.join(FIX, 'Audit.lean'), None or E._workspace())
    assert not info.errors and same == SAME
