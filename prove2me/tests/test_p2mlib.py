"""Unit tests for the p2mlib core (Phase 3)."""
import json
import os

import pytest

from p2mlib import api, leanedit, leaninfo, mission, names, staging, workspace

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures')


def structure():
    return leaninfo.parse(json.load(open(os.path.join(FIX, 'Structure.json'))),
                          open(os.path.join(FIX, 'Structure.lean'), 'rb').read())


# --- names: the prime class -------------------------------------------------------------------
@pytest.mark.parametrize('text,name,hit', [
    ("exact isMarginal_EBad'", 'isMarginal_EBad', False),          # 2026-10-02: \b matched inside the primed name
    ("exact isMarginal_EBad", 'isMarginal_EBad', True),
    ("exact MooreFoelner.isMarginal_EBad h", 'isMarginal_EBad', True),
    ("exact foo₁", 'foo', False),                                   # subscripts continue identifiers
    ("-- uses isMarginal_EBad here\nexact trivial", 'isMarginal_EBad', False),   # comments are not uses
])
def test_mentions(text, name, hit):
    assert names.mentions(text, name) is hit


def test_short_base_qualify():
    assert names.short("A.B.foo''") == "foo''" and names.base("A.B.foo''") == 'foo'
    assert names.qualify('A', 'x') == 'A.x' and names.qualify('A', '_root_.x') == 'x' and names.qualify('', 'x') == 'x'


# --- workspace.published: one copy, comment-aware ------------------------------------------------
def test_published_ignores_comment_lines(tmp_path):
    (tmp_path / 'Theorems').mkdir()
    (tmp_path / 'Theorems' / 'Thm_N_dep.lean').write_text(
        '/-!\ntheorem for balls: a module docstring\n-/\nnamespace N\n\ntheorem dep (h : 1 = 1) : True := by\n  sorry\n\nend N\n')
    pub = workspace.published(str(tmp_path))
    assert pub['dep'].full == 'N.dep' and pub['dep'].module == 'Theorems.Thm_N_dep' and pub['dep'].binders == ['h']
    full, module, binders = pub['dep']                     # tuple-compatible for older callers
    assert 'for' not in pub


# --- mission.load: no module cache --------------------------------------------------------------
def test_mission_load_is_not_cached(tmp_path):
    for n in ('a', 'b'):
        (tmp_path / n).mkdir()
        (tmp_path / n / 'mission.py').write_text("NAMESPACE = %r\n" % n)
    assert mission.load(str(tmp_path / 'a')).NAMESPACE == 'a'
    assert mission.load(str(tmp_path / 'b')).NAMESPACE == 'b'     # not the first mission again


# --- staging: guards ------------------------------------------------------------------------------
def test_fresh_dir_refuses_and_force_never_follows_links(tmp_path):
    shared = tmp_path / 'lib' / 'Keep.lean'
    shared.parent.mkdir()
    shared.write_text('shared')
    d = staging.fresh_dir(str(tmp_path / 'root'), 's')
    os.symlink(str(shared.parent), os.path.join(d, 'Mathlib'))
    with pytest.raises(SystemExit):
        staging.fresh_dir(str(tmp_path / 'root'), 's')
    staging.fresh_dir(str(tmp_path / 'root'), 's', force=True)
    assert shared.exists() and not os.path.exists(os.path.join(d, 'Mathlib'))


# --- api helpers on a fake platform ---------------------------------------------------------------
def test_paginate_offset_and_numbered():
    items = list(range(250))
    off_calls = []

    def call(m, p, b=None):
        off_calls.append(p)
        off = int(p.split('offset=')[1]) if 'offset=' in p else None
        if off is not None:
            return {'x': items[off:off + 100]}
        page = int(p.split('page=')[1])
        return {'x': items[(page - 1) * 100:page * 100], 'total': 250}
    assert api.paginate('/m', 'x', call=call) == items and len(off_calls) == 3
    assert api.paginate_numbered('/s', 'x', call=call) == items


def test_poll_verdict_pending_is_not_rejection():
    r = api.poll_verdict('s', minutes=1, every=30, call=lambda m, p, b=None: {'status': 'PENDING'}, sleep=lambda s: None)
    assert r['status'] == 'PENDING'
    r = api.poll_verdict('s', call=lambda m, p, b=None: {'status': 'ACCEPTED'}, sleep=lambda s: None)
    assert r['status'] == 'ACCEPTED'


def test_live_sketch_edges_skips_deprecated_and_other_theorems():
    g = {'nodes': [{'node_type': 'theorem', 'theorem_id': 'D', 'theorem_name': 'N.dep'},
                   {'node_type': 'sketch', 'submission_id': 'live', 'parent_theorem_id': 'T', 'status': 'ACCEPTED', 'deprecated_at': None},
                   {'node_type': 'sketch', 'submission_id': 'old', 'parent_theorem_id': 'T', 'status': 'ACCEPTED', 'deprecated_at': 'x'},
                   {'node_type': 'sketch', 'submission_id': 'child', 'parent_theorem_id': 'U', 'status': 'ACCEPTED', 'deprecated_at': None}],
         'edges': [{'source': 'D', 'target': 'sketch-live'}]}
    assert api.live_sketch_edges('T', call=lambda m, p, b=None: g) == {'live': {'N.dep'}}


def test_no_frozen_comments(monkeypatch):
    monkeypatch.delenv('P2M_ALLOW_DOCSTRING', raising=False)
    with pytest.raises(SystemExit):
        api.no_frozen_comments({'problems': [{'formal_statement': '-- note\ntheorem t : True := by\n  sorry'}]})
    api.no_frozen_comments({'formal_statement': 'theorem t : "a--b" = "a--b" := by\n  sorry'})


# --- leanedit: by Lean's ranges ---------------------------------------------------------------------
def test_remove_open_in_command_takes_its_prefix():
    info = structure()
    out = leanedit.remove_commands(info, [leanedit.command_of(info, 'A.viaIn')])
    assert 'open Nat in' not in out and 'theorem viaIn' not in out and 'private theorem hidden' in out


def test_remove_section_keeps_balance():
    # the FAmenChild case: removing the declarations inside a section leaves section/variable/end intact
    info = structure()
    out = leanedit.remove_commands(info, [leanedit.command_of(info, 'inSec1'), leanedit.command_of(info, 'inSec2')])
    assert 'section B\nvariable {X : Type} (x : X)\n\nend B' in out


def test_remove_takes_the_comment_above_and_leaves_the_next_one():
    # Lean attaches a `--` comment to the token before it; by command ranges alone, removing f_one
    # left its comment behind and removing viaSimp took the comment introducing viaLemma
    info = structure()
    out = leanedit.remove_commands(info, [leanedit.command_of(info, 'f_one')])
    assert 'an rfl lemma used only through' not in out
    assert 'theorem f_zero : f 0 = 1 := rfl\n\ntheorem viaSimp' in out
    out = leanedit.remove_commands(info, [leanedit.command_of(info, 'viaSimp')])
    assert "theorem f_one : f 1 = 0 := rfl\n\n-- Mathlib's `lemma` is its own command kind" in out


def test_remove_keeps_the_wider_separator():
    # `def g1` / `def g2` / blank / `/-! -/`: removing g2 must not glue g1 to the doc comment
    # (the Moore golden's `def lf` and `/-! #### x0 -/`)
    info = structure()
    out = leanedit.remove_commands(info, [leanedit.command_of(info, 'g2')])
    assert 'def g1 : ℕ := 1\n\n/-! ### Structures -/' in out


def test_prune_plan_on_structure():
    # Lean-dependency pruning: solution's closure, attribute and instance roots stay; unused
    # theorems, Mathlib `lemma`s (no core `declaration` kind) and an `open ... in` prefix go;
    # section/variable/end stay
    from p2mlib import prune
    info = structure()
    drop, imports, rep = prune.plan(info)
    assert rep['removed'] == ['A.hidden', 'A.usesHidden', 'A.viaIn', 'f_one', 'g1', 'g2', 'inSec1',
                              'inSec2', 'unusedLemma', 'viaLemma', 'viaSimp']
    out = prune.apply(info, drop, imports)
    for kept in ("theorem foo'", '@[simp] theorem s1', 'theorem s2', 'section B\nvariable {X : Type} (x : X)',
                 'def f (n', 'theorem f_zero', 'structure P', 'instance : Inhabited P', 'theorem solution'):
        assert kept in out, kept
    assert 'open Nat in' not in out and 'lemma' not in out.replace("Mathlib's `lemma`", '')


def test_replace_and_insert():
    info = structure()
    i = leanedit.command_of(info, 'f_zero')
    assert 'theorem f_zero : f 0 = 1 := by rfl' in leanedit.replace_command(info, i, 'theorem f_zero : f 0 = 1 := by rfl')
    assert '-- inserted\ntheorem f_zero' in leanedit.insert_before(info, i, '-- inserted\n')


def scope_fixture():
    import json, os
    fix = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures')
    return leaninfo.parse(json.load(open(os.path.join(fix, "Scope.json"))), open(os.path.join(fix, "Scope.lean"), "rb").read())


def test_scope_wrap_carries_local_attributes_after_their_namespace():
    # Lodha-Moore S2 (2026-10-02): `attribute [local instance] polishSpace_P1` was not context, and at
    # the top level the namespace was opened only after the context commands, so neither resolved
    info = scope_fixture()
    i = leanedit.command_of(info, 'Sc.uses')
    assert leanedit.scope_wrap(info, i, top_level=True) == ('section\nopen Sc\nattribute [local simp] helper_eq\n', 'end\n')
    assert leanedit.scope_wrap(info, i) == ('section\nnamespace Sc\nattribute [local simp] helper_eq\n', 'end Sc\nend\n')


def test_scope_wrap_opens_every_prefix_of_a_dotted_namespace():
    # F-amenability Monod 5.1 (2026-10-03): a check block in `namespace ThompsonAmenability.M51` got a
    # top-level `open ThompsonAmenability.M51`, which does not open `ThompsonAmenability`, so the
    # published statement's `HC1RatRat` (`ThompsonAmenability.HC1RatRat`) did not resolve
    from types import SimpleNamespace as NS
    src = 'namespace A.B\ntheorem t : True := trivial\nend A.B\n'
    pos = lambda b: NS(byte=b)
    cmds = [NS(start=pos(0), end=pos(13), context=[]),
            NS(start=pos(14), end=pos(41), context=[(0, [])])]
    info = NS(commands=cmds, slice=lambda a, b: src.encode()[a:b].decode())
    assert leanedit.scope_wrap(info, 1, top_level=True) == ('section\nopen A\nopen A.B\n', 'end\n')
    assert leanedit.scope_wrap(info, 1) == ('section\nnamespace A.B\n', 'end A.B\nend\n')


def test_prune_drops_the_include_of_a_dropped_variable():
    # Lodha-Moore S3a (2026-10-02): `variable (hb : HB)` went with HB, `include hb` stayed
    from p2mlib import prune
    info = scope_fixture()
    drop, imports, rep = prune.plan(info)
    out = prune.apply(info, drop, imports)
    assert 'variable (hb : HB)' not in out and 'include hb' not in out and 'theorem solution' in out
