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


def test_roman_numeral_in_parentheses_is_not_first_person(tmp_path):
    # Chou's description, 2026-10-02: "four processes: (I) subgroups, (II) quotients"
    out = check(tmp_path, 'It is closed under four processes: (I) subgroups, (II) quotients.\n')
    assert "first person 'I'" not in out


def test_a_link_on_a_wrapped_line_counts_for_its_sentence(tmp_path):
    # Chou's description wraps its lines; the link sat one line below "published" (2026-10-02)
    out = check(tmp_path, 'On this platform the definition is already published\n'
                          '(the bundle [`B`](https://prove2.me/theorems/x)), with more.\n')
    assert 'without a prove2.me link' not in out


def test_each_list_item_is_its_own_sentence(tmp_path):
    out = check(tmp_path, '- Reused from the Garrido missions\n- See [x](https://prove2.me/theorems/y).\n')
    assert 'without a prove2.me link: …- Reused from the Garrido missions' in out \
        or 'without a prove2.me link: …Reused from the Garrido missions' in out


def test_the_mission_is_this_mission(tmp_path):
    # Monod's description, 2026-10-02: "The mission defines amenability of a relation as ..."
    out = check(tmp_path, 'The mission defines amenability of a relation as Connes–Feldman–Weiss do.\n')
    assert 'without a prove2.me link' not in out


def test_a_link_in_another_clause_of_the_sentence_counts(tmp_path):
    # Chou: "... ([Brin–Squier](…)); both are published and proved, ..." (2026-10-02)
    out = check(tmp_path, 'It has no free subgroup ([B](https://prove2.me/theorems/z)); both are published.\n')
    assert 'without a prove2.me link' not in out
