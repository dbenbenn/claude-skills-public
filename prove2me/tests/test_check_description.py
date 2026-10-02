"""check_description.py warnings and failures."""
import os
import subprocess
import sys

from conftest import SCRIPTS

BASE = ('This mission formalizes A. Author, *Title*, J. 1 (2020) ([doi:10/x](https://doi.org/10/x)).\n\n'
        '## Motivation\n\nText.\n\n## Setting\n\nText.\n\n## Target\n\nText.\n\n')


def check(tmp_path, body):
    p = tmp_path / 'd.md'
    p.write_text(BASE + body)
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'check_description.py'), str(p)],
                       capture_output=True, text=True)
    return r.stdout


def test_unlinked_platform_mission_warns(tmp_path):
    # b16aa34 (dbenbenn): "the Monod mission on this platform" should be a link
    assert 'without a prove2.me link' in check(tmp_path, 'See the Monod mission on this platform.\n')


def test_linked_platform_mission_is_quiet(tmp_path):
    out = check(tmp_path, 'See the [Monod mission](https://prove2.me/missions/Monod) on this platform.\n')
    assert 'without a prove2.me link' not in out


def test_roman_numeral_is_not_first_person(tmp_path):
    # 9f4a09b: "Garrido I" and "Sér. I" were flagged as the pronoun I
    out = check(tmp_path, 'From Garrido I and C. R. Acad. Sci. Paris Sér. I Math. 300.\n')
    assert "first person 'I'" not in out


def test_real_first_person_still_warns(tmp_path):
    assert "first person 'we'" in check(tmp_path, 'Here we prove it.\n')
