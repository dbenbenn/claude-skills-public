"""p2mlib.mission: prose kept as prose/<name>.md (Phase 5), merged into mission.py's items."""
import pytest

from p2mlib import mission

MISSION = '''NAME = "Mini"
DEFINITIONS = [dict(name='Mini', page='1', result='Def 1', tags=[])]
THEOREMS = [dict(name='foo', page='2', result='Lemma 2', tags=[]),
            dict(name='bar', page='3', result='Lemma 3', tags=[], title='Lemma 3 — set in Python', nls='x')]
'''


@pytest.fixture
def mdir(tmp_path):
    (tmp_path / 'mission.py').write_text(MISSION)
    (tmp_path / 'prose').mkdir()
    return tmp_path


def test_prose_files_fill_the_items(mdir):
    (mdir / 'prose' / 'foo.md').write_text(
        "---\ntitle: Lemma 2 — $x$ is fine: really\nmilestone_title: 'Lemma 2 — quoted'\n---\n"
        "If $x \\in A$ then **it** holds.\n\n**Formalization Note.** None.\n\n## Milestone\n\"The source.\" (p. 2)\n")
    (mdir / 'prose' / 'Mini.md').write_text('---\ntitle: The bundle\n---\nNotions of §1.\n')
    M = mission.load(str(mdir))
    foo = M.THEOREMS[0]
    assert foo['title'] == 'Lemma 2 — $x$ is fine: really'            # a colon in the value is kept
    assert foo['milestone_title'] == 'Lemma 2 — quoted'
    assert foo['nls'] == 'If $x \\in A$ then **it** holds.\n\n**Formalization Note.** None.'
    assert foo['milestone_description'] == '"The source." (p. 2)'
    assert M.DEFINITIONS[0]['nls'] == 'Notions of §1.' and M.THEOREMS[1]['nls'] == 'x'


def test_a_field_set_twice_is_refused(mdir):
    (mdir / 'prose' / 'bar.md').write_text('---\ntitle: Lemma 3 — again\n---\n')
    with pytest.raises(SystemExit, match='both in mission.py and in prose/bar.md'):
        mission.load(str(mdir))


def test_a_file_naming_no_item_is_refused(mdir):
    (mdir / 'prose' / 'baz.md').write_text('Text.\n')
    with pytest.raises(SystemExit, match='names no item'):
        mission.load(str(mdir))


def test_old_layout_unchanged(tmp_path):
    (tmp_path / 'mission.py').write_text(MISSION)
    M = mission.load(str(tmp_path))
    assert 'nls' not in M.THEOREMS[0] and M.THEOREMS[1]['title'] == 'Lemma 3 — set in Python'


def test_front_matter_errors():
    with pytest.raises(ValueError):
        mission.front_matter('---\ntitle: x\n')                      # never closed
    with pytest.raises(ValueError):
        mission.front_matter('---\njust text\n---\nbody')
    assert mission.front_matter('no front matter') == ({}, 'no front matter')
