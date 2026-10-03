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


def alias_fixture():
    import json, os
    fix = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures')
    return leaninfo.parse(json.load(open(os.path.join(fix, 'Alias.json'))), open(os.path.join(fix, 'Alias.lean'), 'rb').read())


def test_prune_drops_an_unreached_alias_with_its_target():
    # dense-subgroups (2026-10-03): assemble_blueprint turns each proved stub into `alias foo := NS.Part.foo`;
    # Batteries' `alias` command reports no declId names, so it was never dropped while the declaration
    # it points to was -- the pruned solution failed with "Unknown constant NS.Part.foo"
    from p2mlib import prune
    info = alias_fixture()
    drop, imports, rep = prune.plan(info)
    out = prune.apply(info, drop, imports)
    assert 'alias unused' not in out and 'theorem unused' not in out
    assert 'alias used := Al.P.used' in out and 'theorem used' in out and 'theorem solution' in out
    assert rep['removed'] == ['Al.P.unused', 'Al.unused']
    # a notation command generates parser/macro constants nothing "uses"; it is never pruned (the
    # first version of this fix counted those as declarations and pruned M51's `local notation "E"`)
    assert 'local notation "TT" => True' in out


def variable_fixture():
    import json, os
    fix = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures')
    return leaninfo.parse(json.load(open(os.path.join(fix, 'Variable.json'))), open(os.path.join(fix, 'Variable.lean'), 'rb').read())


def test_prune_drops_only_the_binder_group_naming_a_dropped_declaration():
    # dense-subgroups (2026-10-03), M51 Part D: `variable {R …} {P …} (hP : IsLeftInvariantMean μ R P)` and
    # `variable {Q : Type*}` were dropped because pruned structure fields were named `Data.P`, `Data.Q`,
    # and the kept lemmas of those sections lost R, P, Q. Only a binder group whose type names a pruned
    # declaration goes (`(d : Data X)`), never the command's other binders.
    from p2mlib import prune
    info = variable_fixture()
    drop, imports, rep = prune.plan(info)
    out = prune.apply(info, drop, imports, rep.get('replace'))
    assert 'structure Data' not in out and 'theorem usesD' not in out and 'theorem keepX' not in out
    assert 'variable {X : Type} [Inhabited X]\n' in out and '(d : Data X)' not in out
    assert 'variable {Q : Type} (m : Q → Prop)' in out
    assert 'theorem keepQ' in out and 'theorem solution' in out


def test_dropping_a_theorem_import_keeps_the_bundles_it_brought():
    # dense-subgroups (2026-10-03): Sol_isAmenableRel_orbit_of_isCoamenable lost its unused
    # `import Theorems.Thm_CannonFloydParry_*` lines, and with them the only route to the CFP bundle
    # that kept code needs (`open CannonFloydParry`, `IsDyadic`)
    from p2mlib import prune
    header = 'import Definitions.Def_ThompsonAmenability\nimport Theorems.Thm_CFP_a\nimport Theorems.Thm_M_b\nimport Mathlib\n'
    imports_of = {'Theorems.Thm_CFP_a': ['Mathlib', 'Definitions.Def_CannonFloydParry'],
                  'Theorems.Thm_M_b': ['Mathlib', 'Definitions.Def_ThompsonAmenability', 'Definitions.Def_Monod']}
    assert prune.bundles_to_restore(header, ['Theorems.Thm_CFP_a', 'Theorems.Thm_M_b'], imports_of.get) == [
        'Definitions.Def_CannonFloydParry', 'Definitions.Def_Monod']
    out = prune.restore_bundles(header.replace('import Theorems.Thm_CFP_a\n', '').replace('import Theorems.Thm_M_b\n', ''),
                                ['Definitions.Def_CannonFloydParry', 'Definitions.Def_Monod'])
    assert out == ('import Definitions.Def_ThompsonAmenability\nimport Definitions.Def_CannonFloydParry\n'
                   'import Definitions.Def_Monod\nimport Mathlib\n')


def test_update_drafts_applies_a_delta_to_the_current_file(tmp_path):
    # 2026-10-03: fetch_theorems retired 8 published stubs while submit_all's own fetch_theorems run
    # was in flight; that run wrote back the whole dict it had read a minute earlier, and the 8 were
    # drafts again ("REFUSED: imports draft statements not yet published")
    from p2mlib import workspace as W
    ws = str(tmp_path)
    W.set_drafts({'Theorems.A': '/m', 'Theorems.B': '/m'}, ws)
    stale = W.drafts(ws)                          # a writer's snapshot
    W.update_drafts(remove=['Theorems.A'], ws=ws)  # another writer retires A meanwhile
    stale.pop('Theorems.B')                       # the first writer retires B ...
    W.update_drafts(remove=['Theorems.B'], ws=ws)  # ... and records only its own change
    W.update_drafts(add={'Theorems.C': '/n'}, ws=ws)
    assert W.drafts(ws) == {'Theorems.C': '/n'}


def test_standalone_lib_layout_gets_default_payloads(tmp_path):
    # 2026-10-03: stage_auditor needed a hand-copied payloads() in every standalone mission.py
    (tmp_path / 'mission.py').write_text("THEOREMS = [dict(name='foo')]\nPROSE = {}\n")
    (tmp_path / 'lib').mkdir()
    (tmp_path / 'lib' / 'Thm_foo.lean').write_text(
        'import Mathlib\n\nnamespace N\n\ntheorem foo : True := by\n  sorry\n\nend N\n')
    m = mission.load(str(tmp_path))
    assert m.payloads() == {'foo': ('import Mathlib',
                                    'namespace N\n\ntheorem foo : True := by\n  sorry\n\nend N\n')}
    assert mission.lib_payload(str(tmp_path / 'lib' / 'Thm_foo.lean')) == m.payloads()['foo']


def test_explicit_payloads_win_over_the_lib_default(tmp_path):
    (tmp_path / 'mission.py').write_text("THEOREMS = []\nPROSE = {}\ndef payloads():\n    return {'x': ('a', 'b')}\n")
    (tmp_path / 'lib').mkdir()
    (tmp_path / 'lib' / 'Thm_foo.lean').write_text('import Mathlib\n\ntheorem foo : True := trivial\n')
    assert mission.load(str(tmp_path)).payloads() == {'x': ('a', 'b')}


def test_unused_definition_imports_are_dropped_unless_their_namespace_is_mentioned():
    # Lusin-Novikov standalone (2026-10-03): the root solution kept `import Definitions.Def_Monod_*`,
    # carried over from the merged LN development, though nothing in it used the Monod bundle
    from p2mlib import prune
    header = ('import Definitions.Def_Monod_PiecewiseProjective\nimport Definitions.Def_CFP\n'
              'import Definitions.Def_Used\nimport Theorems.Thm_T\nimport Mathlib\n')
    ns = {'Definitions.Def_Monod_PiecewiseProjective': ['Monod'], 'Definitions.Def_CFP': ['CannonFloydParry'],
          'Definitions.Def_Used': ['U']}
    kept = 'open CannonFloydParry\ntheorem solution : True := trivial\n'     # used only through `open`
    assert prune.unused_bundles(header, {'Definitions.Def_Used'}, kept, ns.get) == [
        'Definitions.Def_Monod_PiecewiseProjective']
    assert prune.unused_bundles(header, set(), 'theorem s := Monod.foo\n', ns.get) == [
        'Definitions.Def_CFP', 'Definitions.Def_Used']
    # a dropped bundle's own imports are not "restored": only dropped theorem imports bring bundles back
    imports_of = {'Definitions.Def_Monod_PiecewiseProjective': ['Mathlib', 'Definitions.Def_Garrido']}.get
    assert prune.bundles_to_restore(header, ['Definitions.Def_Monod_PiecewiseProjective'], imports_of) == []


def test_inline_tactic_macros_expands_uses_and_drops_the_definition():
    # Lodha-Moore (2026-10-03): four solutions refused for a `macro "gp" : tactic` merged in from a
    # development module (CFP §6 had the same with `grp`); the verifier rejects any macro
    from p2mlib import leantext
    text = ('import Mathlib\n\nmacro "gp" : tactic =>\n'
            '  `(tactic| first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)\n\n'
            'theorem a (x : Nat) : True := by\n  gp\n\n'
            "theorem b (gp' : Nat) : True := by\n  have := gp'\n  trivial\n")
    out, names = leantext.inline_tactic_macros(text)
    assert names == ['gp'] and 'macro' not in out
    assert '  (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)\n' in out
    assert "have := gp'" in out
    assert leantext.inline_tactic_macros(out) == (out, [])
