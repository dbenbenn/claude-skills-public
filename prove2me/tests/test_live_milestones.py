"""live_milestones: adding milestones to a live mission and editing them, from .md files.

A standalone theorem published after launch joins a mission as a milestone (Chornyi, T finitely
presented, Garrido I and Chou at full strength, 2026-10-03); its prose lives in a file, never in a
Python string, and the insertion keeps the captain's reading order."""
import pytest

import live_milestones as L


def test_read_spec(tmp_path):
    f = tmp_path / 'm.md'
    f.write_text('---\ntitle: Theorem 2.6 — as printed\ntheorem: Garrido.foo_of_bar\n---\n\n'
                 'Garrido, p. 7: “If $G$ is amenable …”\n\n*Route.* Take $\\bar\\mu$.\n')
    s = L.read_spec(str(f))
    assert s == {'title': 'Theorem 2.6 — as printed', 'theorem': 'Garrido.foo_of_bar',
                 'description': 'Garrido, p. 7: “If $G$ is amenable …”\n\n*Route.* Take $\\bar\\mu$.'}


def test_read_spec_without_front_matter_is_refused(tmp_path):
    f = tmp_path / 'm.md'
    f.write_text('Just a body\n')
    with pytest.raises(ValueError):
        L.read_spec(str(f))


def test_read_spec_title_only_for_an_edit(tmp_path):
    f = tmp_path / 'm.md'
    f.write_text('---\ntitle: Theorem 2.6 (power-set form) — x\n---\n')
    assert L.read_spec(str(f)) == {'title': 'Theorem 2.6 (power-set form) — x', 'description': ''}


MS = [dict(id='a', sort_order=0), dict(id='b', sort_order=1), dict(id='c', sort_order=2),
      dict(id='d', sort_order=3)]


def test_plan_insert_after_a_middle_milestone():
    new, moves = L.plan_insert(MS, 'b', 2)
    assert new == [2, 3]
    assert moves == [('c', 2, 4), ('d', 3, 5)]


def test_plan_insert_after_the_last_needs_no_moves():
    assert L.plan_insert(MS, 'd', 1) == ([4], [])


def test_plan_insert_renumbers_ties_and_gaps_in_reading_order():
    # the platform orders by (sort_order, id); a tie with the anchor, or a gap, must not let a
    # later milestone land between the new ones
    ms = [dict(id='a', sort_order=0), dict(id='b', sort_order=5), dict(id='bb', sort_order=5),
          dict(id='c', sort_order=9)]
    new, moves = L.plan_insert(ms, 'b', 2)
    assert new == [6, 7]
    assert moves == [('bb', 5, 8)]                     # c (9) already follows; it stays


def test_plan_insert_unknown_anchor_is_refused():
    with pytest.raises(KeyError):
        L.plan_insert(MS, 'zz', 1)


def test_linked_theorem_ids():
    ms = [dict(id='a', theorem=dict(id='t1')), dict(id='b', theorem=None), dict(id='c', theorem_id='t3')]
    assert L.linked_theorem_ids(ms) == {'t1', 't3'}
