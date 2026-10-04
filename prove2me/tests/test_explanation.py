"""p2mlib/explanation.py and patch_explanations.py: an accepted proof carries a paper-style explanation.

2026-10-04: 480 of 1053 accepted submissions had no explanation at all (submit_all never passed
one), although prove.md asks for one on every proof, opening with the statement in display math.
"""
import os

from p2mlib import explanation as E

GOOD = """We prove

$$\\neg\\,\\mathrm{IsAmenable}(G_0) \\wedge G_0 \\text{ is finitely presented}.$$

The idea is to compare orbit relations. Suppose $G_0$ is amenable; then its orbit relation is
amenable, and off a countable set it agrees with the orbit relation of $K$, which is not.
"""


def test_a_paper_style_explanation_passes():
    assert E.problems(GOOD) == []


def test_empty_and_too_short_fail():
    assert E.problems('')
    assert E.problems('$$x = 1$$')


def test_the_statement_display_is_required():
    text = GOOD.replace('$$', '$')
    assert any('display' in p for p in E.problems(text))


def test_gendered_pronouns_fail():
    assert any('pronoun' in p for p in E.problems(GOOD + '\nAs he shows in Lemma 2, the map is onto.\n'))


def test_adjectives_the_platform_forbids_fail():
    assert any('elegant' in p for p in E.problems(GOOD + '\nThis elegant trick finishes the proof.\n'))


def test_lean_identifiers_in_backticks_are_not_prose():
    assert E.problems(GOOD + '\nThe hypothesis `he` and the lemma `his_bound` are used.\n') == []


def test_explanation_files_are_found_by_submission_id(tmp_path):
    import patch_explanations as P
    sid = '0ee1c164-4b7c-48b6-852f-fbfc1290aa5d'
    (tmp_path / 'LodhaMoore').mkdir()
    (tmp_path / 'LodhaMoore' / (sid + '.md')).write_text(GOOD)
    (tmp_path / 'LodhaMoore' / 'notes.md').write_text('not an explanation')
    (tmp_path / 'manifest.json').write_text('[]')
    found = P.targets(str(tmp_path))
    assert [s for s, _ in found] == [sid]
    assert os.path.basename(found[0][1]) == sid + '.md'


def test_submit_all_reads_the_mission_explanation_file(tmp_path):
    import submit_all as S
    (tmp_path / 'explanations').mkdir()
    (tmp_path / 'explanations' / 'foo_bar.md').write_text(GOOD)
    assert S.explanation_file(str(tmp_path), 'foo_bar') == str(tmp_path / 'explanations' / 'foo_bar.md')
    assert S.explanation_file(str(tmp_path), 'missing') is None
