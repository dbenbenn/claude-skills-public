"""fetch_theorems.py and publish_standalone.py against a fake platform."""
import json
import os

import pytest

import fetch_theorems as F
import publish_standalone as PS


def test_fetch_writes_server_shape_and_skips_unchanged(tmp_path, monkeypatch, capsys):
    def call(m, p, b=None):
        if p.startswith('/mission-proposals/'):
            return {'items': [{'theorem_name': 'N.t'}, {'definition_name': 'N_defs'}, {'theorem_name': 'N.later'}]}
        if p.startswith('/theorems?theorem_name=N.t'):
            return {'theorems': [{'theorem_name': 'N.t', 'id': 'T'}]}
        if p.startswith('/theorems?theorem_name=N_defs'):
            return {'theorems': [{'theorem_name': 'N_defs', 'id': 'D'}]}
        if p.startswith('/theorems?theorem_name='):
            return {'theorems': []}                                   # not published yet
        if p == '/theorems/T':
            return {'theorem_name': 'N.t', 'status': 'Open', 'preamble': 'import Mathlib',
                    'formal_statement': 'namespace N\n\ntheorem t : True := by\n  sorry\n\nend N'}
        if p == '/theorems/D':
            return {'theorem_name': 'N_defs', 'status': 'Definition', 'definition': 'import Mathlib\n\ndef N.k := 1'}
        raise AssertionError(p)
    monkeypatch.setattr(F, 'call', call)
    monkeypatch.setattr(F.sys, 'argv', ['fetch_theorems.py', '--proposal', 'P', '--out', str(tmp_path)])
    F.main()
    thm = (tmp_path / 'Theorems' / 'Thm_N_t.lean').read_text()
    assert thm == 'import Mathlib\n\nnamespace N\n\ntheorem t : True := by\n  sorry\n\nend N\n'
    assert (tmp_path / 'Definitions' / 'Def_N_defs.lean').read_text().endswith('def N.k := 1\n')
    assert 'not published (yet?): N.later' in capsys.readouterr().out
    before = os.path.getmtime(tmp_path / 'Theorems' / 'Thm_N_t.lean')
    F.main()                                   # second run: the file already matches, left alone
    assert os.path.getmtime(tmp_path / 'Theorems' / 'Thm_N_t.lean') == before


@pytest.fixture
def folder(tmp_path):
    (tmp_path / 'lib').mkdir()
    (tmp_path / 'lib' / 'Def_Bun.lean').write_text('import Mathlib\n\ndef Bun.k : Nat := 1\n')
    (tmp_path / 'lib' / 'Thm_t.lean').write_text('import Definitions.Def_Bun\nimport Mathlib\n\nnamespace Q\n\ntheorem t : Bun.k = 1 := by\n  sorry\n\nend Q\n')
    (tmp_path / 'mission.py').write_text('''NAMESPACE = 'Q'
TAGS = ['x']
DEFINITIONS = [dict(name='Bun', title='A bundle', nls='The bundle.', page='1', result='Def 1')]
THEOREMS = [dict(name='t', page='2', result='Lemma 1')]
PROSE = {'t': dict(title='Lemma 1 — t', nls='It is $1$.')}
def src(page, result, extra=None, ref=None):
    return 'Paper, p. %s, %s' % (page, result)
''')
    return tmp_path


class FakePublisher:
    def __init__(self, queued=None):
        self.posted, self.store, self.queued = [], {}, dict(queued or {})   # queued: {name: job id}

    def call(self, m, p, b=None):
        if m == 'GET' and p.startswith('/theorems?theorem_name='):
            return {'theorems': []}                                          # nothing published yet
        if m == 'GET' and p.startswith('/publish-jobs?status=PENDING'):
            return {'publish_jobs': [{'id': j, 'theorem_name': n} for n, j in self.queued.items()]}
        if m == 'GET' and p.startswith('/publish-jobs?status='):
            return {'publish_jobs': []}
        if m == 'POST' and p == '/submit-definition':
            self.posted.append(('def', b['definition_name']))
            return {'job_id': 'jd'}
        if m == 'POST' and p == '/submit-problem':
            assert 'D1' in self.store, 'statements published before their bundle'
            self.posted += [('thm', x['theorem_name']) for x in b['problems']]
            for x in b['problems']:
                self.store['T1'] = dict(x, status='Open')
            return {'jobs': [{'job_id': 'j1'}]}
        if p in ('/publish-jobs/jd', '/publish-jobs/queued-def'):
            self.store.setdefault('D1', {'status': 'Definition', 'theorem_title': 'A bundle',
                                         'natural_language_statement': 'The bundle.', 'source': 'Paper, p. 1, Def 1'})
            return {'status': 'PUBLISHED', 'theorem_id': 'D1'}
        if p == '/publish-jobs/j1':
            return {'status': 'PUBLISHED', 'theorem_id': 'T1'}
        if p.startswith('/theorems/'):
            return dict(self.store[p.split('/')[2]])
        raise AssertionError((m, p))


def test_publish_bundle_first_then_statement_and_verify(folder, monkeypatch, capsys):
    import p2m
    fake = FakePublisher()
    monkeypatch.setattr(p2m, 'call', fake.call)
    monkeypatch.setattr(PS.time, 'sleep', lambda s: None)
    monkeypatch.setattr(PS.sys, 'argv', ['publish_standalone.py', str(folder)])
    PS.main()
    out = capsys.readouterr().out
    assert fake.posted == [('def', 'Bun'), ('thm', 'Q.t')]
    assert json.loads((folder / 'published_ids.json').read_text()) == {'Def_Bun': 'D1', 'Q.t': 'T1'}
    assert 'title/prose/source match' in out and 'all fields match' in out
    fake.posted.clear()
    PS.main()                                   # a rerun only verifies
    assert fake.posted == []


def test_rerun_waits_on_a_queued_job_instead_of_publishing_twice(folder, monkeypatch, capsys):
    # Lodha-Moore 2026-10-02: the run was killed while the platform sat on the bundle's job for an
    # hour; published_ids.json had nothing, and a rerun would have submitted the bundle again
    import p2m
    import publish_standalone as P
    fake = FakePublisher(queued={'Bun': 'queued-def'})
    monkeypatch.setattr(p2m, 'call', fake.call)
    monkeypatch.setattr(P.time, 'sleep', lambda s: None)
    monkeypatch.setattr(P.sys, 'argv', ['publish_standalone.py', str(folder)])
    P.main()
    assert ('def', 'Bun') not in fake.posted and ('thm', 'Q.t') in fake.posted
