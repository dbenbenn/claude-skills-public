"""A minimal synthetic mission (a bundle, one milestone, a goal) shared by the draft and
decisions tests."""
import pytest

MISSION = r'''import os
from draft import extract_payloads
HERE = os.path.dirname(os.path.abspath(__file__))
NAME = 'Mini'; FIELDS = ['f']; MISSION_TYPE = 'ResearchPaper'; NAMESPACE = 'Mini'
DEFINITIONS = [dict(name='Mini', title='The bundle', nls='Defines $k$.', tags=['x'], page='1', result='Def 1')]
REFERENCES = []
THEOREMS = [
    dict(name='t1', title='Lemma 1 — one', nls='One holds.', tags=['x'], page='2', result='Lemma 1',
         milestone_title='Lemma 1 — one', milestone_description='p. 2: “One holds.”'),
    dict(name='goal', title='Theorem 2 — two', nls='As the paper says, “Two holds.”', tags=['x'], page='3',
         result='Theorem 2', milestone_title='Theorem 2 — two', milestone_description='p. 3: “Two holds.”'),
]
GOAL = 'goal'
def src(page, result, extra=None, ref=None):
    return 'Paper, p. %s, %s' % (page, result)
def payloads():
    return extract_payloads(os.path.join(HERE, 'lib', 'Thm_Mini.lean'), 'Mini', {'Definitions.Def_Mini': ['Mini.k']})
'''


def make_mission(tmp_path):
    tmp_path.mkdir(parents=True, exist_ok=True)
    (tmp_path / 'lib').mkdir()
    (tmp_path / 'readbacks').mkdir()
    (tmp_path / 'mission.py').write_text(MISSION)
    (tmp_path / 'lib' / 'Def_Mini.lean').write_text('import Mathlib\n\nnamespace Mini\n\ndef k : Nat := 1\n\nend Mini\n')
    (tmp_path / 'lib' / 'Thm_Mini.lean').write_text(
        'namespace Mini\n\ntheorem t1 : Mini.k = 1 := by\n  sorry\n\ntheorem goal : 1 + 1 = 2 := by\n  sorry\n\nend Mini\n')
    for n in ('Def_Mini', 't1', 'goal'):
        (tmp_path / 'readbacks' / (n + '.readback.md')).write_text('Read-back of %s.' % n)
    (tmp_path / 'description.md').write_text('This mission formalizes a paper.\n')
    return tmp_path


