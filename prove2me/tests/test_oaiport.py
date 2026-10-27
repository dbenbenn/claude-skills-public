"""p2mlib.oaiport: porting an openai/math result to one file or to workspace modules.

Each test pins a behaviour that went wrong once on a live port (2026-10-18): a bundle declaration
dropped by its last component took OpenAI's own GlobularSet.Hom.id; an anonymous or local/scoped
instance survived and became a second instance; a named instance with a priority read as
anonymous; a dropped declaration left its `… in` modifier to hit the next command; the target
rename hit structure fields, constructors and `| main` cases; a patch that matched twice was applied
anyway; a root-level compatibility lemma clashed across bundles; a restarted queue lost or repeated
attempts. Small fixture files, no Lean, no network."""
import os
import re

import pytest

from p2mlib import oaiport as O

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'oaiport_fixtures')
O_COMPAT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean', 'compat_4_34.lean')


def fix(name):
    return open(os.path.join(FIX, name), encoding='utf-8').read()


# ---------------------------------------------------------------- what a bundle declares

def test_bundle_names_are_full_names_with_instances():
    names, anon = O.bundle_decl_names(fix('bundle.lean'))
    assert {'OAI.Glob.Hom', 'OAI.Glob.Hom.id', 'OAI.Glob.Row', 'OAI.Glob.stated'} <= names
    # a named instance with a priority is named, and a scoped instance counts
    assert 'OAI.Glob.rowNonempty' in names and 'OAI.Glob.scopedInst' in names
    # `_root_.` means the root
    assert 'rootLevelThing' in names
    # the anonymous instance by namespace and header
    assert anon == {('OAI.Glob', 'instance : Inhabited (Row d)')}


# ---------------------------------------------------------------- dropping them from the port

def test_drop_by_full_name_never_by_last_component():
    names, anon = O.bundle_decl_names(fix('bundle.lean'))
    out, dropped = O.drop_declarations(fix('merged.lean'), names, anon)
    # the bundle's own declarations go
    assert 'OAI.Glob.Hom.id' in dropped and 'OAI.Glob.Row' in dropped
    assert not re.search(r'^structure Hom where\n  f : Nat', out, re.M)
    # OpenAI's own Hom.comp and Other.Hom / Other.Hom.id stay (same last components)
    assert 'def comp (a b : Hom)' in out
    assert 'def Hom.id : Hom := ⟨0⟩' in out and 'structure Hom where\n  g : Nat' in out


def test_instances_named_local_scoped_and_anonymous_are_dropped():
    names, anon = O.bundle_decl_names(fix('bundle.lean'))
    out, dropped = O.drop_declarations(fix('merged.lean'), names, anon)
    assert 'rowNonempty' not in out                        # named, with a priority
    assert 'scopedInst' not in out                         # scoped in the bundle, local in the port
    assert 'instance : Inhabited (Row d)' not in out       # anonymous, same header
    assert 'instance : Nonempty (Row 0)' in out            # anonymous, different header: kept
    assert 'rootLevelThing' not in out


def test_a_dropped_declaration_takes_its_in_modifiers_along():
    names, anon = O.bundle_decl_names(fix('bundle.lean'))
    out, _ = O.drop_declarations(fix('merged.lean'), names, anon)
    assert 'theorem stated' not in out
    assert 'attribute [-simp] Nat.add_comm in' not in out and 'omit u in' not in out
    # a modifier above a kept declaration stays
    assert 'open Nat in\ntheorem keptAfterModifier' in out


def test_universe_lists_already_declared_at_the_top_are_stripped():
    text = 'universe u v\n\ntheorem a.{u} : True := trivial\ndef b.{u, w} : Nat := 0\n'
    out = O.strip_declared_universes(text)
    assert 'theorem a : True' in out
    assert 'def b.{u, w}' in out                           # w is not declared: kept as is


# ---------------------------------------------------------------- renaming the target

def test_target_rename_spares_fields_constructors_cases_and_other_names():
    out = O.rename_target(fix('rename.lean'), 'OAI.Fold.main')
    assert 'theorem main_oai : True := helper' in out
    assert 'theorem uses_main : True := main_oai' in out
    assert 'Fold.main_oai' in out and 'OAI.Fold.main_oai' in out
    # a structure field, its assignments (with or without binders, inline), a constructor and a case
    assert '  main : Nat' in out and '  main := 1' in out and '{ main := j' in out
    assert '  | main\n' in out and '| .main => 0' in out
    # field access and Mathlib names untouched
    assert 'c.main = c.main' in out and 'Nat.succ 0' in out
    # another namespace's `main` untouched
    assert 'namespace Elsewhere\ntheorem main : True := trivial\ntheorem uses_other : True := main\n' in out


def test_target_rename_needs_exactly_one_declaration():
    with pytest.raises(O.PortError, match='exactly one'):
        O.rename_target(fix('rename.lean'), 'OAI.Fold.absent')


# ---------------------------------------------------------------- patches

def test_patches_apply_their_count_and_report_every_mismatch():
    files = {'A.lean': 'x := 1\nx := 1\n', 'B.lean': 'y := 2\n'}
    out = O.apply_patches(files, [{'old': 'x := 1\n', 'new': 'x := 3\n', 'count': 2},
                                  {'old': 'y := 2\n', 'new': 'y := 4\n'}])
    assert out == {'A.lean': 'x := 3\nx := 3\n', 'B.lean': 'y := 4\n'}
    with pytest.raises(O.PortError) as e:
        O.apply_patches(files, [{'old': 'x := 1\n', 'new': 'z'}, {'old': 'nowhere', 'new': 'z'}])
    msg = str(e.value)
    assert 'applies 2 times, want 1' in msg and 'applies 0 times, want 1' in msg
    # a later patch may rewrite an earlier one's output (posteriorreplicas: `infer_instance`, then
    # its replacement amended): each is counted against the text as the earlier ones left it
    chain = [{'old': 'y := 2', 'new': 'y := f'}, {'old': 'y := f', 'new': 'y := g'}]
    assert O.apply_patches({'B.lean': 'y := 2\n'}, chain) == {'B.lean': 'y := g\n'}
    # one text works too
    assert O.apply_patches('y := 2\n', [{'old': 'y := 2', 'new': 'y := 5'}]) == 'y := 5\n'


# ---------------------------------------------------------------- the compatibility block

COMPAT = """section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
end OAICompat434
"""


def test_compat_block_in_a_namespace_turns_aliases_into_rewrites():
    block, rewrites = O.compat_block(COMPAT, 'OAI')
    assert block.startswith('namespace OAI\n') and block.rstrip().endswith('end OAI')
    assert 'theorem ite_eq_left' in block
    # an alias inside the namespace would create OAI.Finset and shadow Mathlib's Finset in
    # `open Finset` (CPTSeparation): it becomes a rewrite of the sources instead
    assert 'alias' not in block
    assert rewrites == {'Finset.prod_le_prod₀': 'Finset.prod_le_prod'}
    src = 'exact Finset.prod_le_prod₀ h1 h2\nexact Finset.prod_le_prod₀\' h\n'
    assert O.apply_rewrites(src, rewrites) == "exact Finset.prod_le_prod h1 h2\nexact Finset.prod_le_prod₀' h\n"
    # the old root-level block, on request
    root, rw = O.compat_block(COMPAT, None)
    assert root == COMPAT and rw == {}


def test_the_three_finset_aliases_are_rewritten_in_every_form():
    # ErdosGallai and RepeatedLocalization (2026-10-19) needed hand renames of
    # Finset.prod_le_prod₀ / prod_le_one₀ / one_le_prod₀ (they ran a job copy of port_modules that
    # dropped the aliases without rewriting). Pinned here: qualified uses after `apply`/`exact`, in
    # parentheses, and bare uses under `open Finset`; never a longer name or another namespace's
    block, rw = O.compat_block(open(O_COMPAT, encoding='utf-8').read(), 'OAI')
    assert {'Finset.prod_le_prod₀', 'Finset.prod_le_one₀', 'Finset.one_le_prod₀'} <= set(rw)
    src = ('      apply Finset.prod_le_prod₀\n'
           '    exact le_mul (Finset.one_le_prod₀ (fun l _ => h l))\n'
           '  exact Finset.prod_le_one₀ (fun _ _ => h0 _)\n'
           'open Finset in\n'
           'theorem t : x := prod_le_prod₀ h1 h2\n'
           'theorem u : y := Other.prod_le_prod₀ h\n'
           'theorem v : z := Finset.prod_le_prod₀_aux\n')
    out = O.apply_rewrites(src, rw)
    assert 'apply Finset.prod_le_prod\n' in out and '(Finset.one_le_prod (fun' in out
    assert 'exact Finset.prod_le_one (fun' in out
    assert 'theorem t : x := prod_le_prod h1 h2' in out
    assert 'Other.prod_le_prod₀ h' in out and 'Finset.prod_le_prod₀_aux' in out
    # without `open Finset` a bare name is someone else's and stays
    assert O.apply_rewrites('theorem t : x := prod_le_prod₀ h\n', rw) == 'theorem t : x := prod_le_prod₀ h\n'


# OpenAI's Mathlib (d13f23b) has `TensorProduct.inductionOn z tmul add`, its zero case taken from
# `tmul 0 0`; ours (0df444a) has only `induction_on z zero tmul add`. The port used to rename and
# insert `| zero => simp only [map_zero]` at the `induction` line's indentation: too weak for most
# goals (ComparatorModel, Boone–Higman: `0 ∈ C`, `Commute _ 0`, a `Module.compHom` smul) and
# misplaced when that line is indented differently from its alternatives (Boone–Higman Corners).

def test_tensor_induction_uses_the_compat_eliminator_and_inserts_no_zero_case():
    src = fix('tensor_induction.lean')
    out = O.core_rewrites(src)
    assert 'TensorProduct.inductionOn' not in out and '| zero' not in out
    assert out.count('induction z using OAI.tensorInductionOn with\n') == 3
    assert '  induction w using OAI.tensorInductionOn with\n' in out
    assert '  induction z using OAI.tensorInductionOn\n  · exact' in out
    assert 'OAI.tensorInductionOn z h fun' in out
    # every alternative and bullet is left exactly as OpenAI wrote it
    assert out.replace('OAI.tensorInductionOn', 'TensorProduct.inductionOn') == src
    # ours is left alone, and a root-level compat block means a root-level name
    assert O.core_rewrites('TensorProduct.induction_on z') == 'TensorProduct.induction_on z'
    assert O.core_rewrites('using TensorProduct.inductionOn with', None) == 'using tensorInductionOn with'


# OpenAI's Mathlib (d13f23b) names `FreeGroup.induction_on`'s first case `one`; ours (0df444a) names
# it `C1`, so `induction w using FreeGroup.induction_on with | one => …` fails ("Invalid alternative
# name `one`: Expected `C1`"; Eilenberg–Ganea UnitaryWords, 2026-10-24, and 24 files of openai/math).
# Every use becomes the compat block's `freeGroupInductionOn`, OpenAI's signature and case names.

def test_freegroup_induction_uses_the_compat_eliminator():
    src = ('  induction w using FreeGroup.induction_on with\n  | one => simp\n  | of i => simp\n'
           '  | inv_of i hi => simp [hi]\n  | mul a b ha hb => simp [ha, hb]\n'
           'theorem t : P w := FreeGroup.induction_on w h1 hof hinv hmul\n')
    out = O.core_rewrites(src)
    assert 'FreeGroup.induction_on' not in out
    assert '  induction w using OAI.freeGroupInductionOn with\n  | one => simp\n' in out
    assert out.replace('OAI.freeGroupInductionOn', 'FreeGroup.induction_on') == src
    # other names are left alone, and a root-level compat block means a root-level name
    assert O.core_rewrites('FreeGroup.induction_on_x FreeAddGroup.induction_on') == \
        'FreeGroup.induction_on_x FreeAddGroup.induction_on'
    assert O.core_rewrites('using FreeGroup.induction_on with', None) == 'using freeGroupInductionOn with'


def test_the_compat_block_declares_the_freegroup_eliminator_with_case_one():
    block, _ = O.compat_block(open(O_COMPAT, encoding='utf-8').read())
    m = re.search(r'^@\[elab_as_elim\]\ntheorem freeGroupInductionOn\b(.*?):=', block, re.M | re.S)
    assert m and '(one :' in m.group(1)


def test_the_compat_block_declares_the_eliminator_outside_a_tensorproduct_namespace():
    block, _ = O.compat_block(open(O_COMPAT, encoding='utf-8').read())
    assert re.search(r'^@\[elab_as_elim\]\ntheorem tensorInductionOn\b', block, re.M)
    # an OAI.TensorProduct namespace would capture `open TensorProduct` inside `namespace OAI.…`
    assert not re.search(r'^(theorem|lemma|def|namespace) TensorProduct\b', block, re.M)


@pytest.mark.lean
def test_tensor_induction_shapes_compile_against_the_workspace_mathlib(tmp_path):
    from p2mlib import carve as C
    block, _ = O.compat_block(open(O_COMPAT, encoding='utf-8').read())
    f = tmp_path / 'TensorFix.lean'
    f.write_text('import Mathlib\n\n' + block + '\n' + O.core_rewrites(fix('tensor_induction.lean')),
                 encoding='utf-8')
    out = C.compile_file(str(f), None, str(tmp_path / 'olean'))
    assert 'Ambiguous namespace' not in out, out


def test_the_compat_block_declares_a_simp_lemma_for_numerals_below_infty():
    block, _ = O.compat_block(open(O_COMPAT, encoding='utf-8').read())
    assert re.search(r'^@\[simp\]\ntheorem ofNat_le_infty\b', block, re.M)


@pytest.mark.lean
def test_simp_closes_a_numeral_le_infty_with_the_compat_block(tmp_path):
    from p2mlib import carve as C
    block, _ = O.compat_block(open(O_COMPAT, encoding='utf-8').read())
    f = tmp_path / 'OfNatInfty.lean'
    f.write_text('import Mathlib\nopen scoped ContDiff\n\n' + block + '\n'
                 'example : (2 : WithTop ℕ∞) ≤ ∞ := by simp\n'
                 'example : (3 : WithTop ℕ∞) ≤ ∞ := by simp\n', encoding='utf-8')
    out = C.compile_file(str(f), None, str(tmp_path / 'olean'))
    assert 'error' not in out, out


# ---------------------------------------------------------------- the submit queue's logs

def test_the_queue_rebuilds_each_goal_from_its_log():
    st = O.state_from_log(fix('sub_log.txt'))
    # three finished attempts (the first made outside the queue); the killed one does not count
    assert st == {'attempts': 3, 'verdict': 'ACCEPTED', 'id': 's3', 'msg': ''}
    assert O.state_from_log('') is None
    assert O.classify_attempt('ALREADY-PROVED by someone')[0] == 'REFUSED'
    assert O.classify_attempt('verdict TIMEOUT s9\nnot accepted: timed out')[:2] == ('TIMEOUT', 's9')
    assert O.classify_attempt('verdict WRONG s9\nnot accepted: wrong answer')[0] == 'REJECTED'
    assert O.classify_attempt('submission queued') is None


def test_the_submit_queue_reconciles_from_logs_and_limits_retries(tmp_path):
    import importlib.util
    import json
    spec = importlib.util.spec_from_file_location(
        'oai_submit', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                   'scripts', 'oai_submit.py'))
    S = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(S)
    (tmp_path / 'results').mkdir()
    (tmp_path / 'sub_done.log').write_text(fix('sub_log.txt'))
    (tmp_path / 'sub_slow.log').write_text('=== t\nverdict TIMEOUT s5\nnot accepted: timed out\n')
    (tmp_path / 'results' / 'slow.json').write_text(json.dumps({'target': 'OAI.X.slow', 'secs': 120.0}))
    (tmp_path / 'results' / 'fast.json').write_text(json.dumps({'target': 'OAI.X.fast', 'secs': 30.0}))
    (tmp_path / 'sub_fast.log').write_text('=== t\nverdict TIMEOUT s6\nnot accepted: timed out\n')
    q = S.Queue(str(tmp_path))
    q.reconcile(['done', 'slow', 'fast', 'fresh'])
    st = q.load()
    assert st['done'] == {'attempts': 3, 'verdict': 'ACCEPTED', 'id': 's3', 'msg': ''}
    assert 'fresh' not in st
    # a file over ~90 s gets one attempt; a faster one gets an unchanged retry
    assert q.terminal(st['slow'], 'slow') and not q.terminal(st['fast'], 'fast')
    assert q.terminal(st['done'], 'done')


# ---------------------------------------------------------------- the soundness guard

def test_guard_problems_find_metaprogramming_and_the_prelude_token():
    from p2mlib import leantext as L
    text = ('import Mathlib\n/- prelude in a comment -/\ndef prelude_size : Nat := 1\n'
            'def prelude (n : Nat) : Nat := n\n  local macro "x" : term => `(1)\n'
            'example : X.prelude 1 = 1 := rfl\ndef s : String := "prelude"\n')
    got = [(n, tok) for n, tok, _ in L.guard_problems(text)]
    assert got == [(4, 'prelude'), (5, 'macro'), (6, 'prelude')]


def test_ports_rename_identifiers_the_soundness_guard_refuses():
    # WLTime (2026-10-23): OpenAI's TMConsumer.prelude passed every local check and the published
    # bundle failed on the guard; renamed by hand to preludeCode. Both port routes rename it.
    from p2mlib import leantext as L
    src = {'OAI.G.A': ('A', 'import Mathlib\nnamespace OAI.G\ndef prelude (n : Nat) : Nat := n\n'
                            'theorem prelude_size : prelude 1 = 1 := rfl\nend OAI.G\n'),
           'OAI.G.B': ('B', 'import OAI.G.A\nnamespace OAI.G\ntheorem b : G.prelude 2 = 2 := rfl\nend OAI.G\n')}
    files = O.module_files(src, 'Solutions.G', (), '')
    assert 'def prelude_ (n' in files['A.lean'] and 'prelude_size : prelude_ 1' in files['A.lean']
    assert 'G.prelude_ 2' in files['B.lean']
    assert not any(L.guard_problems(t) for t in files.values())
    assert O.guard_renames('x := prelude 1') == 'x := prelude_ 1'


# ---------------------------------------------------------------- the StdSimplex compatibility shim

# OpenAI's Mathlib (d13f23b) has API on the structure `Convexity.StdSimplex` that ours (0df444a)
# lacks, and takes SimplexCategory.toTop to the structure where ours takes the subtype `stdSimplex`.
# Problem340 (2026-10-24) needed a hand-written shim and 22 hand rewrites; WeakMTW, MatchingEntropy
# and SubpolynomialLp each patched the same two lemmas away by hand.

SIMPLEX_SRC = ('import Mathlib\nimport Mathlib.Geometry.Convex.ConvexSpace.Barycenter\n\n'
               'namespace OAI.S\nopen Convexity\n'
               'theorem r (n : ℕ) : Set.range (fun s : Convexity.StdSimplex ℝ (Fin n) ↦ ⇑s.weights) = '
               'Set.range (fun s : StdSimplex ℝ (Fin n) ↦ ⇑s.weights) := '
               'Convexity.StdSimplex.range_toFun_comp_weights.trans rfl\n'
               'def keep : Set (Fin 2 → ℝ) := stdSimplex ℝ (Fin 2)\n'
               'def MyStdSimplex := 1\ndef StdSimplexLike := MyStdSimplex\nend OAI.S\n')


def test_stdsimplex_detection_and_mode():
    assert O.mentions_stdsimplex(SIMPLEX_SRC)
    assert not O.mentions_stdsimplex('def keep : Set (Fin 2 → ℝ) := stdSimplex ℝ (Fin 2)\ndef MyStdSimplex := 1\n')
    # a missing ConvexSpace module alone also needs the shim (it is what the import provided)
    assert O.mentions_stdsimplex('import Mathlib.Geometry.Convex.ConvexSpace.Barycenter\n')
    assert O.stdsimplex_mode([SIMPLEX_SRC]) == 'structure'          # auto
    assert O.stdsimplex_mode([SIMPLEX_SRC], 'subtype') == 'subtype'
    assert O.stdsimplex_mode([SIMPLEX_SRC], 'off') == 'off'
    assert O.stdsimplex_mode(['def x := 1\n'], 'subtype') == 'off'  # nothing to do
    with pytest.raises(O.PortError, match='stdsimplex'):
        O.stdsimplex_mode([SIMPLEX_SRC], 'bogus')


def test_stdsimplex_rewrites_by_mode():
    # structure mode: the names stay (the shim declares them on Convexity.StdSimplex); the imports
    # of d13f23b-only Mathlib files go
    s = O.stdsimplex_rewrite(SIMPLEX_SRC, 'structure')
    assert 'ConvexSpace.Barycenter' not in s and 'import Mathlib\n' in s
    assert 'Convexity.StdSimplex.range_toFun_comp_weights' in s and 'StdSimplex ℝ (Fin n)' in s
    # subtype mode: every qualified or bare StdSimplex becomes OAI.SStd; nothing longer, nothing
    # lowercase
    t = O.stdsimplex_rewrite(SIMPLEX_SRC, 'subtype')
    assert 'Convexity.StdSimplex' not in t and 'ConvexSpace.Barycenter' not in t
    assert 'fun s : OAI.SStd ℝ (Fin n)' in t and 'OAI.SStd.range_toFun_comp_weights' in t
    assert t.count('OAI.SStd ℝ (Fin n)') == 2
    assert 'stdSimplex ℝ (Fin 2)' in t and 'MyStdSimplex' in t and 'def StdSimplexLike' in t
    assert O.stdsimplex_rewrite(SIMPLEX_SRC, 'off') == SIMPLEX_SRC


def test_stdsimplex_shim_text_is_a_closed_section():
    shim = O.stdsimplex_shim()
    assert shim.startswith('import Mathlib\n')
    body = O.stdsimplex_shim(body=True)
    assert not re.search(r'^import ', body, re.M)
    # merge.py declares `universe u v` at the top of a single file: the shim's own universes must
    # live inside its section, never at the top level
    lines = body.split('\n')
    k = next(i for i, l in enumerate(lines) if l.startswith('noncomputable section StdSimplexCompat'))
    assert all(not l.startswith('universe') for l in lines[:k])
    assert body.rstrip().endswith('end StdSimplexCompat')
    # and the names OpenAI's code uses are all declared (by our Mathlib or by the shim)
    for n in ('range_toFun_comp_weights', 'isEmbedding_toFun_comp_weights', 'homeomorphI',
              'subBarycenter', 'continuous_convexCombPair', 'compactSpace', 'total_of_fintype'):
        assert re.search(r'^\s*(?:noncomputable\s+)?(?:lemma|def|instance|abbrev)\s+%s\b' % n, body, re.M), n


def test_stdsimplex_single_file_inlines_or_imports_the_bundle():
    text = O.stdsimplex_rewrite(SIMPLEX_SRC, 'structure')
    t, imports, block = O.stdsimplex_single(SIMPLEX_SRC, 'auto')
    assert imports == [] and 'noncomputable section StdSimplexCompat' in block
    assert 'ConvexSpace.Barycenter' not in t
    t, imports, block = O.stdsimplex_single(SIMPLEX_SRC, 'auto', use_bundle=True)
    assert imports == ['import ' + O.STDSIMPLEX_BUNDLE] and block == ''
    # a declaration a statement bundle already provides is not declared twice
    t, imports, block = O.stdsimplex_single(SIMPLEX_SRC, 'subtype', drop=({'OAI.SStd.weights'}, set()))
    assert 'OAI.SStd ℝ' in t
    assert 'def weights (s : SStd R X)' not in block and 'def map (g : X → Y)' in block
    assert O.stdsimplex_single('def x := 1\n', 'auto') == ('def x := 1\n', [], '')


def test_core_rewrites_unsuffixed_prod_le_prod_is_primed():
    # d13f23b's one-hypothesis `Finset.prod_le_prod` is our `Finset.prod_le_prod'`; the `₀` form
    # is left for the compat alias rewrite, and primed or longer names are untouched
    src = ("exact Finset.prod_le_prod fun i _ => h i\nexact prod_le_prod fun e _ => h e\n"
           "exact Finset.prod_le_prod₀ h0 h1\nexact Finset.prod_le_prod' h\n"
           "exact Finset.prod_le_prod_of_subset h\nexact List.prod_le_prod h\n")
    out = O.core_rewrites(src)
    assert out == ("exact Finset.prod_le_prod' fun i _ => h i\nexact prod_le_prod' fun e _ => h e\n"
                   "exact Finset.prod_le_prod₀ h0 h1\nexact Finset.prod_le_prod' h\n"
                   "exact Finset.prod_le_prod_of_subset h\nexact List.prod_le_prod h\n")


def test_compat_dite_lemmas_are_rewritable():
    # `(if hp : p then a hp else b hp)` elaborates to eta-expanded lambdas, a higher-order pattern
    # `rw [dite_eq_left h]` cannot match (DepthThree 2026-10-25); state them on `dite p a b`
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    assert 'dite p a b = a h := dif_pos h' in src and 'dite p a b = b h := dif_neg h' in src
    assert 'then a hp else b hp' not in src


def test_mathlib_has_flags_only_missing_mathlib_modules(tmp_path):
    # d13f23b's `Mathlib.Basic.Real.Basic` does not exist here; the module route imports Mathlib
    (tmp_path / 'Mathlib' / 'Data' / 'Real').mkdir(parents=True)
    (tmp_path / 'Mathlib' / 'Data' / 'Real' / 'Basic.lean').write_text('')
    assert O.mathlib_has('Mathlib.Data.Real.Basic', root=str(tmp_path))
    assert not O.mathlib_has('Mathlib.Basic.Real.Basic', root=str(tmp_path))
    assert O.mathlib_has('OAI.Foo', root=str(tmp_path))
    assert O.mathlib_has(O.STDSIMPLEX_MISSING_IMPORTS[0], root=str(tmp_path))


def test_demodule_import_all():
    assert O.demodule('module\nimport all Mathlib.X\npublic import all Mathlib.Y\n\ndef a := 1\n') == \
        'import Mathlib.X\nimport Mathlib.Y\n\ndef a := 1\n'


# OpenAI's Mathlib (d13f23b) has `Finsupp.mapDomain_apply_of_injective hf x a`; ours (0df444a) names
# the same statement `Finsupp.mapDomain_apply` (Markov superreflexivity, 2026-10-25).

def test_mapdomain_apply_of_injective_becomes_mapdomain_apply():
    src = 'exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => h) x i\nsimp [mapDomain_apply_of_injective hf]'
    out = O.core_rewrites(src)
    assert 'Finsupp.mapDomain_apply (fun _ _ h => h) x i' in out
    assert 'mapDomain_apply_of_injective' not in out
    assert O.core_rewrites('Finsupp.mapDomain_apply hf x a') == 'Finsupp.mapDomain_apply hf x a'


# d13f23b has `SimpleGraph.Walk.length_le_bypass_length_iff : p.length ≤ p.bypass.length ↔ p.bypass = p`;
# ours has only the one-way `bypass_eq_self_of_length_le_length_bypass` and `length_bypass_le_length`
# (PlanarFPP minimizing_walk_isPath, 2026-10-25). A `_root_` lemma in the compat block keeps `p.…` dot notation.

def test_compat_has_walk_length_le_bypass_length_iff():
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    assert 'theorem _root_.SimpleGraph.Walk.length_le_bypass_length_iff' in src



# Our `Measure.map f μ` is 0 for a non-AEMeasurable `f` (d13f23b: a Dirac mass), so d13f23b's
# unconditional instance `IsProbabilityMeasure (μ.map f)` is false here and cannot be shimmed. For a
# measurable equivalence it holds, and the compat block has it (Problem336, 2026-10-25).

def test_compat_has_probability_measure_map_equiv_instance():
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    assert 'instance isProbabilityMeasure_map_measurableEquiv' in src
    assert 'isProbabilityMeasure_map_any' not in src


# `import Mathlib` in Compat puts every Mathlib instance in scope of every ported module, which
# OpenAI's own narrow imports never saw. Problem336 IncidenceCirculation (2026-10-25): with
# Mathlib.Analysis.CStarAlgebra.CStarMatrix loaded (our `CStarMatrix` is still a type copy of
# `Matrix`), `ext v e; simp only [Matrix.mul_apply]` on a product of matrices fails. The module
# route can give Compat narrow imports instead (`--compat-imports narrow`).

def test_module_route_compat_can_import_narrowly():
    src = {'OAI.G.A': ('A', 'import Mathlib.Data.Finset.Basic\nnamespace OAI.G\ntheorem a : True := trivial\nend OAI.G\n')}
    wide = O.module_files(src, 'Solutions.G', (), '')
    assert wide['Compat.lean'].startswith('import Mathlib\n\n')
    narrow = O.module_files(src, 'Solutions.G', (), '', compat_imports=O.COMPAT_NARROW_IMPORTS)
    head = narrow['Compat.lean'].split('\n\n')[0]
    assert 'import Mathlib\n' not in narrow['Compat.lean'].split('namespace')[0] + '\n'
    assert all(('import %s' % m) in head for m in O.COMPAT_NARROW_IMPORTS)
    assert O.module_files(src, 'Solutions.G', (), '', compat_imports=['Mathlib.Logic.Basic'])['Compat.lean'].startswith(
        'import Mathlib.Logic.Basic\n\n')


# d13f23b names the nonnegative-factor lemmas `Finset.prod_le_prod_of_subset_of_le_one₀` / `…_of_one_le₀`;
# ours (0df444a) has the same statements without the `₀` (SquareDifference ReflectionLaw, 2026-10-25).

def test_prod_le_prod_of_subset_drops_zero_suffix():
    src = ('  prod_le_prod_of_subset_of_le_one₀ hE (fun _ _ => h)\n'
           'exact Finset.prod_le_prod_of_subset_of_one_le₀ h a b\n'
           'exact Finset.prod_le_prod_of_subset_of_le_one\' h\n')
    out = O.core_rewrites(src)
    assert 'prod_le_prod_of_subset_of_le_one hE' in out
    assert 'Finset.prod_le_prod_of_subset_of_one_le h a b' in out
    assert '₀' not in out
    assert "prod_le_prod_of_subset_of_le_one' h" in out


# d13f23b's `Finset.single_le_prod` (ordered monoid, hypothesis `1 ≤ f i`) is our `Finset.single_le_prod'`
# (SquareDifference PrimaryKernel, 2026-10-25), like prod_le_prod above.

def test_single_le_prod_gets_prime_but_qualified_others_do_not():
    src = ("exact_mod_cast single_le_prod (fun j hj => h j hj) hiT\n"
           "exact Finset.single_le_prod h i\nexact List.single_le_prod h\nexact Multiset.single_le_prod h x\n"
           "exact single_le_prod' h\n")
    out = O.core_rewrites(src)
    assert "cast single_le_prod' (fun" in out
    assert "exact Finset.single_le_prod' h i" in out
    assert "List.single_le_prod h" in out and "Multiset.single_le_prod h x" in out
    assert "single_le_prod'' " not in out and "single_le_prod' h\n" in out


# The unsuffixed `prod_le_prod_of_subset_of_one_le` / `_of_le_one` of d13f23b are the ordered-monoid lemmas
# (hypothesis `1 ≤ f i`), i.e. our primed ones; its `…₀` versions are our unsuffixed ones. The prime must be
# added before the `₀` is dropped (SquareDifference CircleDistance, 2026-10-25).

def test_subset_lemmas_prime_and_zero_suffix_do_not_cross():
    src = ("exact prod_le_prod_of_subset_of_one_le (subset_univ T) h\n"
           "exact Finset.prod_le_prod_of_subset_of_le_one h a b\n"
           "exact prod_le_prod_of_subset_of_le_one₀ hE h\n"
           "exact Finset.prod_le_prod_of_subset_of_one_le₀ hE h\n")
    out = O.core_rewrites(src).split('\n')
    assert out[0] == "exact prod_le_prod_of_subset_of_one_le' (subset_univ T) h"
    assert out[1] == "exact Finset.prod_le_prod_of_subset_of_le_one' h a b"
    assert out[2] == "exact prod_le_prod_of_subset_of_le_one hE h"
    assert out[3] == "exact Finset.prod_le_prod_of_subset_of_one_le hE h"


# d13f23b's `Measure.map_smul c (hf : AEMeasurable f μ)` takes a measurability proof; ours is `map_smul c μ f`
# with none. Dropping the proof argument leaves a bare `Measure.map_smul` for `rw`/`simp`
# (SingleLatticeCovering Isotropy/Desmoothing/GaussianSections, 2026-10-25).

def test_measure_map_smul_drops_measurability_argument():
    src = ("rw [Measure.map_smul _ (by fun_prop),map_add_right_eq_self]\n"
           "rw [Measure.map_smul _ em.measurable.aemeasurable,hrestr]\n"
           "rw [Measure.map_smul _ hf.aemeasurable]\n"
           "simp only [unitSphereLaw,Measure.map_smul _ (sphereIsometryMap_measurable e).aemeasurable]\n"
           "exact Measure.map_smul c μ f\n")
    out = O.core_rewrites(src)
    assert "rw [Measure.map_smul,map_add_right_eq_self]" in out
    assert "rw [Measure.map_smul,hrestr]" in out
    assert "rw [Measure.map_smul]\n" in out
    assert "simp only [unitSphereLaw,Measure.map_smul]" in out
    assert "exact Measure.map_smul c μ f" in out


# `exact Measure.map_smul _ (by fun_prop)` must keep its three explicit arguments (no bare name:
# "typeclass instance problem is stuck"; MemoryPrecision, 2026-10-25).

def test_measure_map_smul_exact_keeps_explicit_arguments():
    out = O.core_rewrites("    exact Measure.map_smul _ (by fun_prop)\n")
    assert "exact Measure.map_smul _ _ _\n" in out


# unifIntegrable_iff' is the definition here (WeakHessian, oaiq-052).

def test_unif_integrable_iff_prime_dropped():
    out = O.core_rewrites("  have hi : UnifIntegrable g 2 m := by\n    rw [unifIntegrable_iff']\n    intro e he\n"
                          "  have h2 : UnifIntegrable g 2 m := by\n    apply unifIntegrable_iff'.mpr\n    intro e he\n")
    assert "unifIntegrable_iff'" not in out and out.count("intro e he") == 2


# A term-mode use after `:=` (same line or next) takes the two other explicit arguments as `_ _` too
# (WeakHessian SpeedApprox/RnDerivSmul, oaiq-052).

def test_measure_map_smul_term_mode_after_assign():
    out = O.core_rewrites("  have he : a = b :=\n    Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable\n"
                          "  _ = c := Measure.map_smul C hf.aemeasurable\n")
    assert "Measure.map_smul _ _ _\n" in out
    assert "Measure.map_smul C _ _\n" in out


# d13f23b: `AddSubgroup.isClosed_of_discreteTopology (U := L)`; ours: `AddSubgroup.isClosed_of_discrete (H := L)`
# (SingleLatticeCovering GridCounts/CircuitErrors, 2026-10-25).

def test_isclosed_of_discretetopology_renamed():
    src = ("exact AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)\n"
           "    L.module.toAddSubgroup.isClosed_of_discreteTopology\n")
    out = O.core_rewrites(src)
    assert "AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)" in out
    assert "toAddSubgroup.isClosed_of_discrete\n" in out
    assert 'Topology' not in out


# `namespace A.B` closed by `end B` leaves `A` open. The carver's scope mirror counts a dotted namespace as
# one scope, so the declarations after the `end B` lost `A` (Zarankiewicz OrderedExteriorPaths,
# "Unknown identifier FiniteIntersectionDrawing" in a bundle, 2026-10-25). The port opens the components
# as separate namespaces when (and only when) a shorter `end` closes the dotted one.

def test_partially_closed_dotted_namespace_is_split():
    src = ("namespace OAI\nnamespace Zarankiewicz.DrawingPassages\nvariable (x : Nat)\nend DrawingPassages\n"
           "namespace PolygonalExterior\nend PolygonalExterior\nend Zarankiewicz\nend OAI\n")
    out = O.core_rewrites(src)
    assert "namespace Zarankiewicz\nnamespace DrawingPassages\n" in out
    assert "namespace Zarankiewicz.DrawingPassages" not in out
    whole = "namespace A.B\ndef x := 1\nend A.B\nnamespace C.D\nend D\nend C\n"
    out = O.core_rewrites(whole)
    assert out.startswith("namespace A.B\ndef x := 1\nend A.B\n")
    assert "namespace C\nnamespace D\nend D\nend C" in out


# d13f23b has `Set.equivOfEq h : s ≃ t`; ours calls it `Equiv.setCongr h` (QuarticPowerFree Jacobians, 2026-10-25).

def test_set_equiv_of_eq_becomes_setcongr():
    out = O.core_rewrites("(Equiv.ofInjective j hjj).trans (Set.equivOfEq hJr)\nexact Set.equivOfEq_foo\n")
    assert "(Equiv.setCongr hJr)" in out
    assert "Set.equivOfEq_foo" in out


# d13f23b's `ContinuousLinearMap.nonneg_iff_isPositive` has the operator implicit (`.mp hT` works); ours takes it
# explicitly (Kirchberg–Rørdam Representations, 2026-10-25).

def test_nonneg_iff_ispositive_gets_explicit_argument():
    src = ("have ht := ContinuousLinearMap.nonneg_iff_isPositive.mp hT\n"
           "exact LinearMap.nonneg_iff_isPositive.mpr h\n"
           "rw [ContinuousLinearMap.nonneg_iff_isPositive T]\n")
    out = O.core_rewrites(src)
    assert "(ContinuousLinearMap.nonneg_iff_isPositive _).mp hT" in out
    assert "(LinearMap.nonneg_iff_isPositive _).mpr h" in out
    assert "nonneg_iff_isPositive T]" in out


# d13f23b's `ContinuousLinearMap.le_def` / `LinearMap.le_def` have f g implicit (`.mp hgap` works); ours takes
# them explicitly (NuclearUltrapower SOSGap, 2026-10-26).

def test_le_def_gets_explicit_arguments():
    src = ("have hp := (ContinuousLinearMap.le_def.mp hgap).re_inner_nonneg_right y\n"
           "apply ContinuousLinearMap.le_def.mpr\n"
           "rw [LinearMap.le_def]\n"
           "exact ContinuousLinearMap.le_def_foo\n")
    out = O.core_rewrites(src)
    assert "(ContinuousLinearMap.le_def _ _).mp hgap" in out
    assert "apply (ContinuousLinearMap.le_def _ _).mpr" in out
    assert "rw [LinearMap.le_def]" in out
    assert "le_def_foo" in out and "le_def _ _)_foo" not in out


# d13f23b: `CStarAlgebra.norm_le_norm_of_le_of_nonneg (hab) (ha)`; ours: `norm_le_norm_of_nonneg_of_le (ha) (hab)`
# (Kirchberg–Rørdam, 2026-10-25). A compat lemma with d13f23b's argument order.

def test_compat_has_cstar_norm_le_norm_of_le_of_nonneg():
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    assert 'theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg' in src
    assert 'Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order' in O.COMPAT_NARROW_IMPORTS


# d13f23b has `MvPolynomial.monomial_mul_monomial` (ours: `MvPolynomial.monomial_mul`); QuarticPowerFree
# uses it under `open MvPolynomial` (2026-10-25). A compat theorem with the new name.

def test_compat_has_mvpolynomial_monomial_mul_monomial():
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    assert 'theorem _root_.MvPolynomial.monomial_mul_monomial' in src
    assert 'Mathlib.Algebra.MvPolynomial.Basic' in O.COMPAT_NARROW_IMPORTS


# d13f23b: `CStarAlgebra.norm_mem_spectrum_of_nonneg a ha`; ours has `a` implicit (Kirchberg–Rørdam, 2026-10-25).

def test_norm_mem_spectrum_of_nonneg_drops_explicit_element():
    src = ("exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg b hb)\n"
           "exact CStarAlgebra.norm_mem_spectrum_of_nonneg hb\n")
    out = O.core_rewrites(src)
    assert "(CStarAlgebra.norm_mem_spectrum_of_nonneg hb)" in out
    assert out.count("norm_mem_spectrum_of_nonneg hb") == 2


# d13f23b: `CStarAlgebra.norm_or_neg_norm_mem_spectrum a ha`; ours has `a` implicit (FactorGeneration, 2026-10-26).

def test_norm_or_neg_norm_mem_spectrum_drops_explicit_element():
    src = ("rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a ha with h | h\n"
           "exact CStarAlgebra.norm_or_neg_norm_mem_spectrum ha\n")
    out = O.core_rewrites(src)
    assert out.count("norm_or_neg_norm_mem_spectrum ha") == 2


# d13f23b: `CStarAlgebra.star_mul_le_algebraMap_norm_sq a`; ours has `a` implicit (FactorGeneration, 2026-10-26).

def test_star_mul_le_algebraMap_norm_sq_drops_explicit_element():
    src = ("sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq a)\n"
           "(CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := x))\n")
    out = O.core_rewrites(src)
    assert "(CStarAlgebra.star_mul_le_algebraMap_norm_sq)" in out
    assert "star_mul_le_algebraMap_norm_sq (a := x)" in out


# d13f23b has `YoungDiagram.card_transpose`; ours does not (BinarySweep DiagonalDimension, 2026-10-25).

def test_compat_has_youngdiagram_card_transpose():
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    assert 'theorem _root_.YoungDiagram.card_transpose' in src
    assert '@[simp]\ntheorem _root_.YoungDiagram.card_transpose' in src  # d13f23b's is a simp lemma
    assert 'Mathlib.Combinatorics.Young.YoungDiagram' in O.COMPAT_NARROW_IMPORTS


# d13f23b finds `IsProbabilityMeasure (μ.map f)` for every f (its Measure.map is total). The measurable projections
# and the subtype coercion are common enough to shim (SphericalPerceptron Entropy_Quantile, 2026-10-25).

def test_compat_has_probability_map_instances_for_projections():
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    for name in ('isProbabilityMeasure_map_fst', 'isProbabilityMeasure_map_snd', 'isProbabilityMeasure_map_subtype_val'):
        assert 'instance ' + name in src


# ---------------------------------------------------------------- the batch-3 rewrites, pinned (2026-10-25)
# The rewrites of Kirchberg–Rørdam, SingleLatticeCovering, SquareDifference, QuarticPowerFree and
# SphericalPerceptron went in one at a time; their tests were the one example each. These pin what a rewrite
# must not do: change a neighbour, be applied twice, or miss a spelling of the same call.

BATCH3_SOURCE = (
    "exact Finset.prod_le_prod_of_subset_of_one_le (subset_univ T) h\n"
    "exact Finset.single_le_prod h i\n"
    "exact Finset.prod_le_prod h1 h2\n"
    "rw [Measure.map_smul _ (sphereIsometryMap_measurable e).aemeasurable]\n"
    "rw [MeasureTheory.Measure.map_smul _ (h (f x)).aemeasurable]\n"
    "exact (AddSubgroup.isClosed_of_discreteTopology (U := L))\n"
    "exact (Equiv.ofInjective j hjj).trans (Set.equivOfEq hJr)\n"
    "have ht := ContinuousLinearMap.nonneg_iff_isPositive.mp hT\n"
    "exact CStarAlgebra.norm_mem_spectrum_of_nonneg b hb\n"
    "exact Finsupp.mapDomain_apply_of_injective hf x\n")


def test_core_rewrites_applied_twice_change_nothing_more():
    # (not `prod_le_prod_of_subset_of_le_one₀`: d13f23b's name for our unsuffixed lemma, which a second
    # pass would prime as it does d13f23b's unsuffixed one)
    once = O.core_rewrites(BATCH3_SOURCE)
    assert once != BATCH3_SOURCE
    assert O.core_rewrites(once) == once


def test_the_measurability_argument_may_be_a_parenthesised_application():
    # `(h (f x)).aemeasurable`: one level of nested parentheses (SphericalPerceptron, 2026-10-25)
    out = O.core_rewrites("rw [MeasureTheory.Measure.map_smul _ (h (f x)).aemeasurable]\n"
                          "rw [Measure.map_smul _ (g x).aemeasurable, a]\n")
    assert "rw [MeasureTheory.Measure.map_smul]\n" in out
    assert "rw [Measure.map_smul, a]\n" in out


def test_batch3_rewrites_leave_their_neighbours_alone():
    src = ("exact Measure.map_smul c μ f\n"
           "exact Measure.map_smul_apply c\n"
           "exact Subgroup.isClosed_of_discrete h\n"
           "exact Set.equivOfEq_foo\n"
           "exact Finset.single_le_prod' h i\n"
           "exact prod_le_prod_of_subset_of_le_one' h a b\n"
           "exact CStarAlgebra.norm_mem_spectrum_of_nonneg hb\n"
           "exact Finsupp.mapDomain_apply hf x\n")
    assert O.core_rewrites(src) == src


def test_the_element_argument_of_norm_mem_spectrum_ends_with_its_line():
    # a call with only the positivity proof, followed by the next line, took the proof for the element
    # and the next line's first word for the proof ("norm_mem_spectrum_of_nonneg exact Finsupp…")
    out = O.core_rewrites("exact CStarAlgebra.norm_mem_spectrum_of_nonneg hb\nexact foo x\n"
                          "exact CStarAlgebra.norm_mem_spectrum_of_nonneg b hb\n")
    assert out == "exact CStarAlgebra.norm_mem_spectrum_of_nonneg hb\nexact foo x\n" \
                  "exact CStarAlgebra.norm_mem_spectrum_of_nonneg hb\n"


@pytest.mark.lean
def test_the_batch3_rewrites_and_compat_lemmas_elaborate_against_the_workspace_mathlib(tmp_path):
    # the rewritten forms exist in our Mathlib with the shapes the rewrites assume, and each compat lemma
    # is usable as d13f23b's (simp lemma, instance found by search, argument order)
    from p2mlib import carve as C
    block, _ = O.compat_block(open(O_COMPAT, encoding='utf-8').read())
    f = tmp_path / 'Rewrites.lean'
    f.write_text('import Mathlib\n\n' + block + '\n' + O.core_rewrites(fix('rewrite_targets.lean')),
                 encoding='utf-8')
    C.compile_file(str(f), None, str(tmp_path / 'olean'))


# d13f23b's `eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf` takes an AEStronglyMeasurable proof; ours has
# only the two hypotheses (MemoryPrecision FiniteDensity/PointwiseMain/MeasurableTests, 2026-10-25).

def test_elpnorm_rpow_enorm_drops_measurability_argument():
    src = ("    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast (by omega : p \u2260 0))\n"
           "      (by finiteness) hG.ennreal_toReal.aestronglyMeasurable]\n"
           "  erw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp) (by finiteness)\n"
           "      hFc.aestronglyMeasurable,\n"
           "    eLpNorm_eq_lintegral_rpow_enorm_toReal hpE (by finiteness)]\n")
    out = O.core_rewrites(src)
    assert "p \u2260 0))\n      (by finiteness)]" in out
    assert "(by finiteness),\n" in out
    assert "aestronglyMeasurable" not in out
    assert "eLpNorm_eq_lintegral_rpow_enorm_toReal hpE (by finiteness)]" in out


# d13f23b has `spectralRadius_eq_of_unital` (the spectral radius as the supremum over the spectrum); ours has only
# the definition (BrownMeasure, StructuralCrouzeix, NumericalRange, 2026-10-25). A compat theorem with the new name.

def test_compat_has_spectral_radius_eq_of_unital():
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    assert 'theorem spectralRadius_eq_of_unital' in src


# d13f23b's `eLpNorm_one_eq_lintegral_enorm hf` takes an AEStronglyMeasurable proof; ours has none
# (MemoryPrecision JointL1/LabelTranslations, 2026-10-25). The argument may be a long parenthesised term and may
# follow named arguments such as `(f := ...)`.

def test_elpnorm_one_drops_measurability_argument():
    src = ("rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hFm.aestronglyMeasurable]\n"
           "rw [\u2190 eLpNorm_one_eq_lintegral_enorm\n"
           "  ((show Measurable (fun p : \u03a9 \u00d7 Y => F (p.1, p.2 + \u03b4 \u2022 u))\n"
           "    from by fun_prop).aestronglyMeasurable)]\n"
           "rw [eLpNorm_one_eq_lintegral_enorm\n"
           "  (f := fun point => a point - F point)\n"
           "  (haverage.aestronglyMeasurable.sub hF.aestronglyMeasurable)]\n"
           "exact (eLpNorm_one_eq_lintegral_enorm (by fun_prop)).symm\n"
           "simp [eLpNorm_one_eq_lintegral_enorm, foo]\n")
    out = O.core_rewrites(src)
    assert "rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm]" in out
    assert "rw [\u2190 eLpNorm_one_eq_lintegral_enorm]" in out
    assert "rw [eLpNorm_one_eq_lintegral_enorm\n  (f := fun point => a point - F point)]" in out
    assert "exact (eLpNorm_one_eq_lintegral_enorm).symm" in out
    assert "simp [eLpNorm_one_eq_lintegral_enorm, foo]" in out


# d13f23b's `Filter.eventuallyEmptyOrUniv_iff'` is our `Filter.eventuallyConst_set'` (same statement,
# `s =ᶠ[l] ∅ ∨ s =ᶠ[l] univ`; FiniteFactor TorusErgodic, 2026-10-25).

def test_eventually_empty_or_univ_renamed():
    out = O.core_rewrites("  rw [Filter.eventuallyEmptyOrUniv_iff']\n  exact foo.eventuallyEmptyOrUniv_iff'.mp h\n")
    assert "rw [Filter.eventuallyConst_set']" in out
    assert "foo.eventuallyConst_set'.mp h" in out


# d13f23b renames (StandardMap, 2026-10-25): `StrictMono.range_inj_of_wellFoundedLT` is our `StrictMono.range_inj`;
# `TopologicalSpace.NonemptyCompacts.dist_eq` is `Metric.NonemptyCompacts.dist_eq`;
# `TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const x` is `Metric.lipschitz_infDist_set x`.

def test_range_inj_and_nonempty_compacts_renames():
    src = ("exact (f.strictMono.range_inj_of_wellFoundedLT g.strictMono).mp hh\n"
           "rw [← TopologicalSpace.NonemptyCompacts.dist_eq] at hh\n"
           "have := TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const x\n")
    out = O.core_rewrites(src)
    assert "f.strictMono.range_inj g.strictMono" in out
    assert "range_inj_of_wellFoundedLT" not in out
    assert "← Metric.NonemptyCompacts.dist_eq" in out
    assert "Metric.lipschitz_infDist_set x" in out


# `convert h using n; ring` (OpenAI) leaves, in ours, instance-diamond / lambda-form goals before the ring goal
# (UnitDistances, Mahler, 2026-10-25): close every goal with `rfl` or `ring`.

def test_convert_using_semicolon_ring_closes_all_goals():
    src = "    convert hBern using 1; ring\n  have x := 1\n    convert h using 2; ring_nf\n    convert h using 1; simp\n"
    out = O.core_rewrites(src)
    assert "convert hBern using 1 <;> first | rfl | ring\n" in out
    assert "convert h using 2; ring_nf" in out and "convert h using 1; simp" in out


def test_convert_using_semicolon_parenthesised_first_closes_all_goals():
    # KServer (oaiq-017, 2026-10-26): `convert h using 1; (first | rfl | ring)` runs only on the first goal
    src = "    convert hm using 1; (first | rfl | ring)\n    convert h using 1; (first | rfl | simp)\n"
    out = O.core_rewrites(src)
    assert "convert hm using 1 <;> first | rfl | ring\n" in out
    assert "convert h using 1; (first | rfl | simp)" in out


# d13f23b renames/signatures (UnitDistances, StandardMap 2026-10-25): `finsum_le_finsum` (ordered monoid, finite
# supports) is our `finsum_le_finsum'`; `Filter.eventuallyEqSet_iff` is `Filter.eventuallyEq_set`;
# `posLog_le_posLog` asks `-1 ≤ x` there and `0 ≤ x` here.

def test_finsum_eventuallyeq_set_posLog_renames():
    src = ("apply finsum_le_finsum (hf) (hg)\nexact finsum_le_finsum' h\n"
           "rw [Filter.eventuallyEqSet_iff]\n"
           "have h' := (posLog_le_posLog (neg_one_lt_zero.le.trans (v.nonneg x)) hxy).trans h\n")
    out = O.core_rewrites(src)
    assert "apply finsum_le_finsum' (hf) (hg)" in out and "finsum_le_finsum'' " not in out
    assert "Filter.eventuallyEq_set" in out and "eventuallyEqSet_iff" not in out
    assert "posLog_le_posLog (id (v.nonneg x))" in out


def test_initialize_token_is_refused_and_renamed_even_as_a_field():
    # VariableWL (2026-10-26): OpenAI's `theorem Machine.initialize` and `M.initialize` were rejected by
    # the soundness guard ("`initialize` - arbitrary code execution at module initialization") in
    # every piece, after every local check had passed
    from p2mlib import leantext as L
    text = 'theorem Machine.initialize (M : Nat) : M = M := rfl\nexample := by rw [M.initialize, M.initial_x]\n'
    assert [(n, t) for n, t, _ in L.guard_problems(text)] == [(1, 'initialize'), (2, 'initialize')]
    out = O.guard_renames(text)
    assert 'Machine.initialize_ ' in out and 'M.initialize_,' in out and 'M.initial_x' in out
    assert not L.guard_problems(out)


# d13f23b's `RKHS.posSemidef_tfae` has four items (index 3 = Hermitian and nonneg on `X →₀ V`);
# ours has three, with that form at index 2 (HotSpots Reciprocal, 2026-10-26).

def test_rkhs_posSemidef_tfae_index():
    out = O.core_rewrites("apply (RKHS.posSemidef_tfae.out 1 3).mpr\nexact (RKHS.posSemidef_tfae.out 0 1).mp h\n")
    assert "apply (RKHS.posSemidef_tfae.out 2 0).mp" in out
    assert "RKHS.posSemidef_tfae.out 0 1" in out


# d13f23b's `eLpNorm_restrict_eq_of_support_subset` takes a measurability argument first and
# `eLpNorm_congr_norm_ae` two; ours take none (HotSpots Sobolev, 2026-10-26).

def test_elpnorm_measurability_args_dropped():
    src = ("rw [eLpNorm_restrict_eq_of_support_subset hf.continuous.aestronglyMeasurable hs']\n"
           "apply eLpNorm_congr_norm_ae\n  (hf.continuous_fderiv (by simp)).aestronglyMeasurable\n"
           "  (((a b).symm.continuous.comp\n    (hf.continuous_fderiv (by simp))).aestronglyMeasurable)\n  hh\n")
    out = O.core_rewrites(src)
    assert "eLpNorm_restrict_eq_of_support_subset hs'" in out
    assert "eLpNorm_congr_norm_ae\n  hh" in out.replace("  hh", "  hh") or "eLpNorm_congr_norm_ae hh" in out


def test_elpnorm_le_mul_measurability_arg_dropped():
    out = O.core_rewrites("apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul\n  (measurable_green_left x).aestronglyMeasurable\nfilter_upwards [h] with y hy\n")
    assert "eLpNorm_le_mul_eLpNorm_of_ae_le_mul\nfilter_upwards" in out or "eLpNorm_le_mul_eLpNorm_of_ae_le_mul\n  \nfilter" in out


# Mathlib's `Matroid` file declares the global token `<m` (strict minor). `1<m` (a variable named m)
# lexes as `1 <m` and fails; OpenAI's Mathlib has no such token (CompleteCrossing 2026-10-26).
def test_lt_m_token_is_spaced():
    assert O.core_rewrites('by_cases hm : 1<m\n') == 'by_cases hm : 1 < m\n'
    assert O.core_rewrites('(s w\').card<m := by') == "(s w').card < m := by"
    assert O.core_rewrites('i<m ∧ j≤m') == 'i < m ∧ j ≤ m'
    # the Matroid notation itself, written with spaces, stays
    assert O.core_rewrites('N <m M') == 'N <m M'
    assert O.core_rewrites('a <mem b') == 'a <mem b'


# d13f23b's `birkhoffSum_succ_apply'` / `birkhoffSum_add_right_apply` are our `birkhoffSum_succ'` / `birkhoffSum_add`
# (StandardMap Lyapunov, 2026-10-26).

def test_birkhoff_sum_renames():
    out = O.core_rewrites("rw [birkhoffSum_succ_apply', hb]\nsimpa using birkhoffSum_add_right_apply T g m n x\nrw [birkhoffSum_succ_apply]\n")
    assert "rw [birkhoffSum_succ', hb]" in out
    assert "birkhoffSum_add T g m n x" in out
    assert "rw [birkhoffSum_succ]" in out
    out = O.core_rewrites("simp only [birkhoffSum_zero_apply, x]\nrw [birkhoffSum_succ_apply, ih]\n")
    assert "simp only [birkhoffSum_zero, x]" in out
    assert "rw [birkhoffSum_succ, ih]" in out
    assert O.core_rewrites('(node i<minus i)') == '(node i < minus i)'


def test_measure_map_smul_drops_named_aemeasurable_lemma_application():
    out = O.core_rewrites("rw [potentialMeasure,Measure.map_smul _ (chart_aemeasurable e d),map_chartMeasure e d hd]\n")
    assert "rw [potentialMeasure,Measure.map_smul,map_chartMeasure e d hd]" in out
    assert O.core_rewrites('(hs : 2≤s) (p.val<s-1) a≤c') == '(hs : 2 ≤ s) (p.val < s-1) a ≤ c'


# unqualified `(nonneg_iff_isPositive).mpr` under `open ContinuousLinearMap` (MultipleMixing HilbertCodes, 2026-10-26)

def test_nonneg_iff_ispositive_unqualified_gets_explicit_argument():
    out = O.core_rewrites("exact foo ((nonneg_iff_isPositive).mpr h) (nonneg_iff_isPositive.mp k) (nonneg_iff_isPositive T)\n")
    assert "((nonneg_iff_isPositive _).mpr h)" in out
    assert "(nonneg_iff_isPositive _).mp k" in out
    assert "(nonneg_iff_isPositive T)" in out


# d13f23b's `compProd_map_condDistrib hX hY` has our `compProd_map_condDistrib hY`; and
# `condDistrib_ae_eq_of_measure_eq_compProd` (ae-measurable) is a compat lemma (MultipleMixing Arrays, 2026-10-26).

def test_comp_prod_map_cond_distrib_drops_first_arg_and_compat_lemma():
    out = O.core_rewrites("exact (compProd_map_condDistrib hE.aemeasurable hO.aemeasurable).symm\n"
                          "  (compProd_map_condDistrib (μ := μ i) (X := f i)\n    (Y := id) (hf i).aemeasurable measurable_id.aemeasurable).symm\n"
                          "(compProd_map_condDistrib (by fun_prop) measurable_id.aemeasurable).symm\n")
    assert "(compProd_map_condDistrib hO.aemeasurable).symm" in out
    assert "(Y := id) measurable_id.aemeasurable).symm" in out
    assert "(compProd_map_condDistrib measurable_id.aemeasurable).symm" in out
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean', 'compat_4_34.lean')).read()
    assert 'theorem condDistrib_ae_eq_of_measure_eq_compProd' in src


def test_isometry_lipschitzWith_and_aemeasurable_of_eval():
    import os
    out = O.core_rewrites("exact U.isometry.lipschitzWith\nexact AEMeasurable.of_eval fun n => h n\n")
    assert "U.isometry.lipschitz\n" in out
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean', 'compat_4_34.lean')).read()
    assert 'theorem _root_.AEMeasurable.of_eval' in src


def test_convert_closes_instance_diamond_first():
    src = ("  have h := 1\n  convert (foo x\n      (bar y)) using 1\n  rfl\n"
           "  · convert hh using 2\n    simp\n"
           "  convert h using 1\n  · simp\n  convert h using 1; first | rfl | field_simp\n")
    out = O.core_rewrites(src)
    assert "using 1\n  all_goals try with_reducible_and_instances rfl\n  rfl\n" in out
    assert "convert hh using 2\n    all_goals try with_reducible_and_instances rfl\n    simp" in out
    assert "convert h using 1\n  · simp" in out
    assert "convert h using 1 <;> first | rfl | field_simp" in out
    assert O.core_rewrites(out) == out


def test_logderiv_fun_forms_renamed():
    out = O.core_rewrites("rw [logDeriv_fun_mul (f:=a) z h, logDeriv_fun_prod h2 h3, logDeriv_fun_zpow]")
    assert out == "rw [logDeriv_mul (f:=a) z h, logDeriv_prod h2 h3, logDeriv_fun_zpow]"


# d13f23b's `IsChain.linearOrder` takes an `IsChain (· < ·)`; ours an `IsChain (· ≤ ·)` (Coboundary Windows, 2026-10-26).

def test_ischain_lt_of_le_linearOrder():
    out = O.core_rewrites("let : LinearOrder (s : Set P) := hchain.lt_of_le.linearOrder\n")
    assert "hchain.linearOrder\n" in out


def test_compat_has_finset_equivOfEq():
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean', 'compat_4_34.lean')).read()
    assert 'def _root_.Finset.equivOfEq' in src


def test_eLpNorm_le_of_ae_bound_drops_measurability():
    src = "have hh := eLpNorm_le_of_ae_bound (μ := μ) (p := (1 : ℝ≥0∞))\n  (h.integrable x).aestronglyMeasurable\n  (Eventually.of_forall b)\n"
    out = O.core_rewrites(src)
    assert "aestronglyMeasurable" not in out and "(Eventually.of_forall b)" in out and "(μ := μ)" in out


def test_is_local_min_on_renamed_to_localize():
    assert O.core_rewrites("hm.isLocalMinOn.hasFDerivWithinAt_nonneg x; hM.isLocalMaxOn") == \
        "hm.localize.hasFDerivWithinAt_nonneg x; hM.localize"
    assert O.core_rewrites("IsLocalMinOn f s a") == "IsLocalMinOn f s a"


def test_unfold_infer_instance_falls_back_to_map_measurability():
    src = "open MeasureTheory\n  unfold gumbelLaw\n  infer_instance\n  unfold a\n  simp\n"
    out = O.core_rewrites(src)
    assert "  unfold gumbelLaw\n  first | infer_instance | exact Measure.isProbabilityMeasure_map (by %s)\n" % O.AEM_TAC in out
    assert "unfold a\n  simp" in out
    assert O.core_rewrites(out) == out


def test_probability_measure_constructor_instance_falls_back():
    src = "open MeasureTheory\n  ⟨(μ.map f),\n    by infer_instance⟩\n  ⟨x.map g, inferInstance⟩\n"
    out = O.core_rewrites(src)
    assert out.count("(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by %s))⟩" % O.AEM_TAC) == 2
    assert O.core_rewrites(out) == out


def test_sigma_iota_comp_desc_renamed():
    assert O.core_rewrites("exact Sigma.ι_comp_desc _ _; simp [Sigma.ι_comp_desc_assoc]") == \
        "exact Sigma.ι_desc _ _; simp [Sigma.ι_desc_assoc]"


# d13f23b's `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop hf` has a third, measurability argument;
# ours has two (Elasticity Regularity, 2026-10-26)

def test_elpnorm_lt_top_iff_drops_measurability_argument():
    src = ("rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top\n"
           "    (by norm_num) (by norm_num) growth.1.continuous.aestronglyMeasurable]\n"
           "rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h0 h1 hf.aestronglyMeasurable, foo]\n"
           "rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h0 h1]\n")
    out = O.core_rewrites(src)
    assert "rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top\n    (by norm_num) (by norm_num)]" in out
    assert "rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h0 h1, foo]" in out
    assert "rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h0 h1]" in out


# d13f23b's `eLpNorm_exponent_top hf` takes a measurability argument; ours takes none (Elasticity Parameters, 2026-10-26)

def test_elpnorm_exponent_top_drops_measurability_argument():
    src = ("rw [one_mul, Lp.norm_toLp, eLpNorm_exponent_top g.memLp_top.aestronglyMeasurable]\n"
           "rw [eLpNorm_exponent_top (f := g) hg, eLpNorm_exponent_top]\n")
    out = O.core_rewrites(src)
    assert "rw [one_mul, Lp.norm_toLp, eLpNorm_exponent_top]" in out
    assert "rw [eLpNorm_exponent_top (f := g), eLpNorm_exponent_top]" in out


# d13f23b's `Subgroup.isMulCommutative_closure` wants `∀ x ∈ k, ∀ y ∈ k, x ≠ y → x * y = y * x`;
# ours has no `x ≠ y` binder, so the `rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ _` after `apply` has one `_` too
# many ("introN failed"; Boone–Higman SteinbergPresentation, PeriodicGroups MonomialPresentation,
# FiniteType SteinbergWords).

def test_is_mul_commutative_closure_rintro_drops_the_ne_binder():
    src = ('  apply Subgroup.isMulCommutative_closure\n  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ _\n  exact h u v\n')
    assert O.core_rewrites(src) == \
        '  apply Subgroup.isMulCommutative_closure\n  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩\n  exact h u v\n'
    src2 = '  apply Subgroup.isMulCommutative_closure\n  rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩ _\n'
    assert O.core_rewrites(src2).splitlines()[1] == '  rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩'
    # other rintro lines are untouched
    other = '  apply foo\n  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ _\n'
    assert O.core_rewrites(other) == other



# ---------------------------------------------------------------- total Measure.map, the rest of the shapes
# d13f23b's `Measure.map` is total, so `IsProbabilityMeasure (μ.map f)` is an instance for every f; ours
# needs AEMeasurable. Synthetic snippets shaped like the sites oaiq-005 (Brenier, SmoothObstruction,
# CompactFactors) fixed by hand: 2026-10-26.

FALLBACK = "first | infer_instance | exact Measure.isProbabilityMeasure_map (by %s)" % O.AEM_TAC


def test_aem_chain_tries_the_context_after_fun_prop():
    # the chain names, in order, what fun_prop cannot do: a hypothesis (also under a binder), a
    # Continuous / MeasurePreserving / QuasiMeasurePreserving hypothesis, measurability
    t = O.AEM_TAC
    assert t.startswith('first | fun_prop')
    for need in ('assumption', 'Measurable.aemeasurable', 'solve_by_elim', 'Continuous.aemeasurable',
                 'MeasurePreserving.aemeasurable', 'QuasiMeasurePreserving.aemeasurable', 'measurability',
                 'continuous_eval_const'):
        assert need in t, need
    assert t.index('fun_prop') < t.index('assumption') < t.index('measurability')


def test_have_let_haveI_of_isprobabilitymeasure_by_inferinstance_get_the_fallback():
    # Brenier AffineOptimality, ConditionalLimits, Functions, GridCells ...
    src = ("  let : IsProbabilityMeasure (Measure.map T ρ) := inferInstance\n"
           "  have : IsProbabilityMeasure (Measure.map T ρ) := inferInstance\n"
           "  haveI : IsProbabilityMeasure (μ.map p) := by infer_instance\n"
           "    have : IsProbabilityMeasure ν := inferInstance\n"
           "  letI hν : IsProbabilityMeasure ν := inferInstance\n")
    out = O.core_rewrites(src)
    assert "  let : IsProbabilityMeasure (Measure.map T ρ) := by %s\n" % FALLBACK in out
    assert "  have : IsProbabilityMeasure (Measure.map T ρ) := by %s\n" % FALLBACK in out
    assert "  haveI : IsProbabilityMeasure (μ.map p) := by %s\n" % FALLBACK in out
    assert "    have : IsProbabilityMeasure ν := by %s\n" % FALLBACK in out
    assert "  letI hν : IsProbabilityMeasure ν := by %s\n" % FALLBACK in out
    assert 'inferInstance' not in out.replace('infer_instance', '')
    assert O.core_rewrites(out) == out                                      # idempotent


def test_other_instances_by_inferinstance_are_left_alone():
    src = "  have : Fintype X := inferInstance\n  let i : Nonempty X := by infer_instance\n"
    assert O.core_rewrites(src) == src


def test_lone_infer_instance_lines_and_anonymous_constructors_get_the_fallback():
    # Brenier MapDistance/Midpoint/Quantization, PlaneSpectrum SpectralMeasure; MapTransport/Coupling
    src = ("open MeasureTheory\n"
           "    infer_instance\n"
           "  refine ⟨inferInstance, ?_, ?_⟩\n"
           "  refine ⟨q, hqY, inferInstance, ?_,\n"
           "    inferInstance,\n"
           "    inferInstance, ?_, ?_, ?_⟩\n")
    out = O.core_rewrites(src)
    assert "    %s\n" % FALLBACK in out
    assert out.count("(by %s)" % FALLBACK) == 4
    assert "inferInstance" not in out
    assert O.core_rewrites(out) == out


def test_inferinstance_in_a_file_without_measure_theory_is_left_alone():
    # NuclearUltrapower FullGroupAlgebra: `⟨x, ℂ, inferInstance, 1, rfl⟩` is a CStarAlgebra witness; the fallback
    # chain made its type a metavariable and timed out at whnf (2026-10-26)
    src = "  exact ⟨‖evaluate 1 x‖, ℂ, inferInstance, 1, rfl⟩\n    infer_instance\n"
    assert O.core_rewrites(src) == src


def test_map_smul_drops_a_proof_that_is_a_chain_and_keeps_the_first_argument():
    # Brenier Cube/Midpoint/PrefixSampling; DensityBounds/SymbolCores (`C hr.aemeasurable`, `a hS.measurable.aemeasurable`)
    src = ("    Measure.map_smul _ (PiLp.volume_preserving_ofLp (Fin d)).measurable.aemeasurable,\n"
           "  rw [Measure.map_smul _ (tripleSplit h).continuous.measurable.aemeasurable]\n"
           "    rw [←hcoords,Measure.map_smul C hr.aemeasurable,hrecover] at h\n"
           "  rwa [Measure.map_smul a hS.measurable.aemeasurable,hS.map_eq] at hh\n"
           "  rw [Measure.map_smul ((μ : Measure G) (e.coset z))⁻¹\n"
           "    (f := fun point : ℂ => point + -v) (continuous_id.add_const (-v)).aemeasurable,\n"
           "      foo]\n")
    out = O.core_rewrites(src)
    assert "    Measure.map_smul,\n" in out
    assert "  rw [Measure.map_smul]\n" in out
    assert "rw [←hcoords,Measure.map_smul C,hrecover] at h" in out
    assert "rwa [Measure.map_smul a,hS.map_eq] at hh" in out
    assert "rw [Measure.map_smul ((μ : Measure G) (e.coset z))⁻¹\n    (f := fun point : ℂ => point + -v),\n      foo]" in out
    assert 'aemeasurable' not in out


def test_map_smul_exact_with_a_chain_proof_keeps_three_explicit_arguments():
    out = O.core_rewrites("    exact Measure.map_smul ((μ : Measure G) (e.coset z))⁻¹\n"
                          "      (e.measurable_coordinate.comp (measurable_id.div_const z)).aemeasurable\n")
    assert "exact Measure.map_smul ((μ : Measure G) (e.coset z))⁻¹ _ _\n" in out


def test_map_smul_with_no_proof_argument_is_untouched():
    src = "  rw [Measure.map_smul c μ f, Measure.map_smul c]\n  simp [Measure.map_smul]\n"
    assert O.core_rewrites(src) == src


def test_probabilitymeasure_map_gets_its_measurability_proof():
    # Brenier/SmoothObstruction: `let v (n : ℕ) : ProbabilityMeasure X := μ.map (b n)`; explicit form
    src = ("  let v (n : ℕ) : ProbabilityMeasure X := μ.map (b n)\n"
           "  let w : ProbabilityMeasure Y := ProbabilityMeasure.map μ f\n")
    out = O.core_rewrites(src)
    assert "  let v (n : ℕ) : ProbabilityMeasure X := μ.map (f := (b n)) (by %s)\n" % O.AEM_TAC in out
    assert "  let w : ProbabilityMeasure Y := ProbabilityMeasure.map μ (f := f) (by %s)\n" % O.AEM_TAC in out
    assert O.core_rewrites(out) == out
    # with a proof already given, or a Measure (not ProbabilityMeasure) map, nothing changes
    same = ("  let a : ProbabilityMeasure Y := μ.map hf.aemeasurable\n  let b : Measure Y := μ.map f\n"
            "  let c : ProbabilityMeasure Y := ProbabilityMeasure.map μ hf.aemeasurable\n")
    assert O.core_rewrites(same) == same


def test_fst_map_prodmk_drops_its_first_measurability_argument():
    # CompactFactors AlgebraModels: d13f23b `Measure.fst_map_prodMk hq measurable_id`, ours takes only the second
    out = O.core_rewrites("  simpa only [Measure.fst_map_prodMk hq measurable_id, Measure.fst_compProd] using he\n")
    assert "Measure.fst_map_prodMk measurable_id," in out


# OpenAI's Mathlib (d13f23b) states `UnifIntegrable` with extended-real ε, δ and has
# `unifIntegrable_iff`; ours (0df444a) has the real-ε definition and no such iff (SLE IntegralLimits,
# ExponentialMartingales, oaiq-027). `unifIntegrable_iff.mpr ?_` becomes the compat block's
# `unifIntegrable_of_enn`, which takes the same extended-real hypothesis.

def test_unif_integrable_iff_mpr_uses_the_compat_lemma():
    src = '  refine ⟨unifIntegrable_iff.mpr ?_, C, ?_⟩\n  apply MeasureTheory.unifIntegrable_iff.mpr\n'
    out = O.core_rewrites(src)
    assert out == '  refine ⟨OAI.unifIntegrable_of_enn ?_, C, ?_⟩\n  apply OAI.unifIntegrable_of_enn\n'
    assert O.core_rewrites('unifIntegrable_iff.mpr', None) == 'unifIntegrable_of_enn'
    assert O.core_rewrites('unifIntegrable_iff\'.2') == 'unifIntegrable_iff\'.2'


def test_the_compat_block_declares_unif_integrable_of_enn():
    block, _ = O.compat_block(open(O_COMPAT, encoding='utf-8').read())
    assert re.search(r'^theorem unifIntegrable_of_enn\b', block, re.M)


def test_clm_lipschitzWith_field_becomes_lipschitz():
    # d13f23b's `ContinuousLinearMap.lipschitzWith` (GeneralMahler, 2026-10-26): ours is `.lipschitz`
    out = O.core_rewrites("exact (l.lipschitzWith.comp hK).add (q.root.toContinuousLinearMap.lipschitzWith)\n"
                          "apply lipschitzWith_of_nnnorm_deriv_le\nexact hf.lipschitzWith_foo\n")
    assert "l.lipschitz.comp hK" in out
    assert "toContinuousLinearMap.lipschitz)" in out
    assert "apply lipschitzWith_of_nnnorm_deriv_le" in out
    assert "hf.lipschitzWith_foo" in out


# d13f23b's Egorov `tendstoUniformlyOn_of_ae_tendsto'` takes an extended-real ε (`0 < ENNReal.ofReal e`);
# ours takes the real ε>0 (CAT0Fillings LargePieces, oaiq-029).

def test_egorov_real_epsilon():
    src = ("  obtain ⟨e,he,hμe,hue⟩ := tendstoUniformlyOn_of_ae_tendsto'\n"
           "    (fun n => (hu n).stronglyMeasurable) stronglyMeasurable_const hc\n"
           "      (ENNReal.ofReal_pos.mpr (half_pos hε))\n")
    out = O.core_rewrites(src)
    assert "hc\n      (half_pos hε)\n" in out
    assert "ofReal_pos" not in out


# d13f23b's `PosSemidef.dotProduct_mulVec_zero_iff` has `x` implicit; ours takes it explicitly
# (CAT0Fillings Determinant, oaiq-029).

def test_posSemidef_dotProduct_mulVec_zero_iff_explicit_x():
    out = O.core_rewrites("    have hz := hP.dotProduct_mulVec_zero_iff.1 heq.symm\n")
    assert "(hP.dotProduct_mulVec_zero_iff _).1 heq.symm" in out


def test_posSemidef_dotProduct_mulVec_zero_iff_parenthesised_receiver():
    # DimensionTen FamilyGeometry (oaiq-033): `(hA i).…` and `(hAB i).1.…`
    out = O.core_rewrites("exact (hA i).dotProduct_mulVec_zero_iff.mp hi\nhave hz := (hAB i).1.dotProduct_mulVec_zero_iff.mp h\n")
    assert "exact ((hA i).dotProduct_mulVec_zero_iff _).mp hi" in out
    assert "have hz := ((hAB i).1.dotProduct_mulVec_zero_iff _).mp h" in out
    assert O.core_rewrites(out) == out


def test_clm_isTopologicalAddGroup_becomes_inferInstance():
    # d13f23b's named instance `ContinuousLinearMap.isTopologicalAddGroup` (GeneralMahler, 2026-10-26)
    out = O.core_rewrites("    let : IsTopologicalAddGroup (E →L[ℝ] F) :=\n      ContinuousLinearMap.isTopologicalAddGroup\n")
    assert "      inferInstance\n" in out
    assert "isTopologicalAddGroup" not in out.replace("IsTopologicalAddGroup", "")


# d13f23b has `NonUnitalStarRingHom.ofClass f`; ours has no such name, and the coercion
# `(f : _ →⋆ₙ+* _)` needs its types written. The compat block's `nonUnitalStarRingHomOfClass`
# takes the class instance (Kadison commutator, FreeSymmetry10, oaiq-039; Kaplansky quotient, oaiq-015).

def test_nonunital_star_ring_hom_of_class_uses_the_compat_shim():
    import os
    out = O.core_rewrites("((NonUnitalStarRingHom.ofClass f).map_le_map_of_map_star hab)\n")
    assert "((OAI.nonUnitalStarRingHomOfClass f).map_le_map_of_map_star hab)" in out
    assert O.core_rewrites("NonUnitalStarRingHom.ofClass f", None) == "nonUnitalStarRingHomOfClass f"
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean', 'compat_4_34.lean')).read()
    assert 'def nonUnitalStarRingHomOfClass' in src


# d13f23b's `Isometry.antilipschitzWith` is `Isometry.antilipschitz` in our Mathlib
# (HyperbolicGroups GeometricSpaceTransport, oaiq-034).

def test_core_rewrites_isometry_antilipschitzWith_is_antilipschitz():
    src = "  (u X).symm.isometry.antilipschitzWith.properSpace h\n  hf.antilipschitzWith\n  Isometry.antilipschitzWith hf\n"
    out = O.core_rewrites(src)
    assert '.isometry.antilipschitz.properSpace' in out
    assert 'Isometry.antilipschitz hf' in out
    assert 'hf.antilipschitzWith' in out  # not an isometry: left alone
    assert O.core_rewrites(out) == out


# `SimplexCategory.toTopHomeo` takes the realization of Δ[n] to the subtype `stdSimplex` here and to
# the structure `Convexity.StdSimplex` in d13f23b (TripleGlobe/Thomason, oaiq-043, 2026-10-27: 22 uses
# in one module alone, each needing a hand bridge). Ports in structure mode call the shim's
# `toTopHomeoD` instead, declared in the module StdSimplexTopCompat.

TOPHOMEO_SRC = ('import Mathlib\nnamespace OAI.T\nopen Convexity\n'
                'def f (n : ℕ) (x : |Δ[n]|) : StdSimplex ℝ (Fin (n + 1)) := (SimplexCategory.mk n).toTopHomeo x\n'
                'example (j : SimplexCategory) := j.left.toTopHomeo.symm\n'
                'theorem t := SimplexCategory.toTopHomeo_naturality_apply\n'
                'def keep := myToTopHomeo\ndef keep2 := toTopHomeoD\nend OAI.T\n')


def test_tophomeo_is_renamed_in_structure_mode_only():
    s = O.stdsimplex_rewrite(TOPHOMEO_SRC, 'structure')
    assert '(SimplexCategory.mk n).toTopHomeoD x' in s and 'j.left.toTopHomeoD.symm' in s
    assert 'SimplexCategory.toTopHomeoD_naturality_apply' in s
    assert 'myToTopHomeo' in s and 'toTopHomeoD' in s and 'toTopHomeoDD' not in s
    assert 'toTopHomeo ' not in s.replace('toTopHomeoD', '')
    assert 'toTopHomeo' in O.stdsimplex_rewrite(TOPHOMEO_SRC, 'subtype')
    assert 'toTopHomeoD_naturality' not in O.stdsimplex_rewrite(TOPHOMEO_SRC, 'subtype')


def test_module_route_adds_the_tophomeo_module_where_used():
    src = {'OAI.G.A': ('A', TOPHOMEO_SRC),
           'OAI.G.B': ('B', 'import OAI.G.A\nnamespace OAI.G\ndef g (n : ℕ) : StdSimplex ℝ (Fin (n+1)) := default\nend OAI.G\n')}
    files = O.module_files(src, 'Solutions.G', (), '')
    assert 'import Solutions.G.StdSimplexTopCompat' in files['A.lean']
    assert 'StdSimplexTopCompat' not in files['B.lean']
    top = files['StdSimplexTopCompat.lean']
    assert 'import Solutions.G.StdSimplexCompat' in top and '@MOD@' not in top
    assert 'def SimplexCategory.toTopHomeoD' in top and 'theorem SimplexCategory.toTopHomeoD_naturality_apply' in top
    assert 'sorry' not in top
    files = O.module_files({'OAI.G.A': ('A', SIMPLEX_SRC)}, 'Solutions.G', (), '')
    assert 'StdSimplexTopCompat.lean' not in files


# d13f23b's `MvPowerSeries.pderiv i` takes the index only; ours is `MvPowerSeries.pderiv R i` with the
# ring explicit (SharpRamsey RichLines, oaiq-045). Lemma names (`pderiv_X`, `pderiv_coe`) are untouched.
def test_mv_power_series_pderiv_gets_the_ring_argument():
    src = ('(MvPowerSeries.pderiv i (MvPowerSeries.pderiv j h)) simp [MvPowerSeries.pderiv_X] '
           'MvPowerSeries.pderiv a\n  (f)')
    out = O.core_rewrites(src)
    assert out.count('MvPowerSeries.pderiv _ ') == 3
    assert 'MvPowerSeries.pderiv_X' in out
    assert O.core_rewrites(out) == out


def test_compat_has_finsupp_mapdomain_fintype():
    # d13f23b's `Finsupp.mapDomain_fintype` (Thomason Polyhedra, oaiq-043): `mapDomain f v` as a sum
    import os
    src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                            'compat_4_34.lean')).read()
    assert '_root_.Finsupp.mapDomain_fintype' in src and '∑ i, Finsupp.single (f i) (v i)' in src


# ---------------------------------------------------------------- eLpNorm-family argument drift
# Signatures checked against both Mathlibs (d13f23b via `git show` in the workspace's mathlib checkout; ours 0df444a):
# d13f23b's `eLpNorm_eq_eLpNorm' hp0 hptop hf`, `eLpNorm_nnreal_eq_eLpNorm' hp hf`, `eLpNorm_mono_real hf h` and
# `Lp.eLpNorm_le_of_ae_tendsto bound hf hg h_tendsto` take a measurability proof ours does not (oaiq-038, oaiq-048).

def test_elpnorm_eq_elpnorm_prime_drops_its_third_argument():
    src = ("  rw [eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num) hmeas,\n"
           "    eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num)\n"
           "      (hmeas ds), ENNReal.toReal_ofNat]\n"
           "  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmem.aestronglyMeasurable]\n"
           "  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)\n"
           "    (by norm_num)] using h\n")
    out = O.core_rewrites(src)
    assert out == ("  rw [eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num),\n"
                   "    eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num), ENNReal.toReal_ofNat]\n"
                   "  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]\n"
                   "  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)\n"
                   "    (by norm_num)] using h\n")


def test_a_dropped_argument_never_comes_from_the_next_tactic():
    # a two-argument call at the end of its line: the next line is a new tactic, not a third argument
    src = ("  have h := eLpNorm_eq_eLpNorm' hp0 hptop\n"
           "  exact foo\n"
           "  have h2 := eLpNorm_mono_real\n"
           "  hb\n"
           "  exact eLpNorm_nnreal_eq_eLpNorm' hp\n"
           "  simp\n")
    assert O.core_rewrites(src) == src


def test_elpnorm_nnreal_and_mono_real_drop_their_measurability_argument():
    src = ("      (eLpNorm_nnreal_eq_eLpNorm' (p:=(n:NNReal)) (by exact_mod_cast hn.ne') hsm)\n"
           "    simpa using (eLpNorm_nnreal_eq_eLpNorm' (p := 2) (by norm_num) hf)\n"
           "    eLpNorm_mono_real (hm n).aestronglyMeasurable (hdom n)\n"
           "  apply (eLpNorm_mono_real\n"
           "    (continuous_matrix (fun _ _ => (hp _).smooth.continuous)).aestronglyMeasurable\n"
           "    (fun y => splitMatrix_norm_le _ e)).trans\n"
           "  have hb := eLpNorm_mono_real (μ:=law) (p:=p) hg hb\n")
    out = O.core_rewrites(src)
    assert out == ("      (eLpNorm_nnreal_eq_eLpNorm' (p:=(n:NNReal)) (by exact_mod_cast hn.ne'))\n"
                   "    simpa using (eLpNorm_nnreal_eq_eLpNorm' (p := 2) (by norm_num))\n"
                   "    eLpNorm_mono_real (hdom n)\n"
                   "  apply (eLpNorm_mono_real\n"
                   "    (fun y => splitMatrix_norm_le _ e)).trans\n"
                   "  have hb := eLpNorm_mono_real (μ:=law) (p:=p) hb\n")


def test_lp_elpnorm_le_of_ae_tendsto_drops_the_limit_measurability():
    src = ("  have he := Lp.eLpNorm_le_of_ae_tendsto (.of_forall hbound) hFm hmeas hlim\n"
           "  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hb)\n"
           "    (fun index => (hm index).aestronglyMeasurable)\n"
           "    (Measure.measurable_rnDeriv γ s).ennreal_toReal.aestronglyMeasurable\n"
           "  apply Eventually.of_forall\n"
           "  refine (Lp.eLpNorm_le_of_ae_tendsto (C := c) ?_ (fun j => Lp.aestronglyMeasurable (f j)) hg hl)\n"
           "  apply eLpNorm_le_of_ae_tendsto a b c d\n")
    out = O.core_rewrites(src)
    assert out == ("  have he := Lp.eLpNorm_le_of_ae_tendsto (.of_forall hbound) hFm hlim\n"
                   "  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hb)\n"
                   "    (fun index => (hm index).aestronglyMeasurable)\n"
                   "  apply Eventually.of_forall\n"
                   "  refine (Lp.eLpNorm_le_of_ae_tendsto (C := c) ?_ (fun j => Lp.aestronglyMeasurable (f j)) hl)\n"
                   "  apply eLpNorm_le_of_ae_tendsto a b c d\n")


# ours ADDS a measurability argument to `eLpNorm_sum_le` (hfs), `eLpNorm_le_eLpNorm_of_exponent_le` (hf) and the
# Bochner `tendsto_integral_of_L1'` (hfi). It goes in by name, so its place among the positional arguments does not
# matter, with a tactic that finds it (oaiq-038, oaiq-048).

def test_added_measurability_arguments_go_in_by_name():
    src = ("        exact eLpNorm_sum_le hp_enn\n"
           "    have h := eLpNorm_sum_le (f := f) (s := s) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)\n"
           "    _ ≤ eLpNorm v 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)\n"
           "  apply (eLpNorm_le_eLpNorm_of_exponent_le (μ:=μ) (f:=g) hp).trans\n"
           "  tendsto_integral_of_L1' f (Eventually.of_forall hu) (tendsto_eLpNorm_one hf hu hlim)\n"
           "    tendsto_integral_of_L1' Y\n")
    out = O.core_rewrites(src)
    sum_tac = "(hfs := fun _ _ => by %s)" % O.AESM_TAC
    one_tac = "(hf := by %s)" % O.AESM_TAC
    assert ("exact eLpNorm_sum_le %s hp_enn\n" % sum_tac) in out
    assert ("eLpNorm_sum_le %s (f := f)" % sum_tac) in out
    assert ("eLpNorm_le_eLpNorm_of_exponent_le %s (by norm_num)\n" % one_tac) in out
    assert ("(eLpNorm_le_eLpNorm_of_exponent_le %s (μ:=μ)" % one_tac) in out
    assert ("tendsto_integral_of_L1' (hfi := by %s) f (Eventually" % O.AESM_TAC) in out
    assert ("tendsto_integral_of_L1' (hfi := by %s) Y\n" % O.AESM_TAC) in out
    assert O.core_rewrites(out) == out


def test_added_measurability_argument_not_inserted_where_already_given():
    # the vector-measure `tendsto_integral_of_L1' f hfi …` already took `hfi` in d13f23b; a name inside a longer
    # name, `@`-explicit uses and an already named argument are left alone
    src = ("  exact tendsto_integral_of_L1' f hf.aestronglyMeasurable hFi hF\n"
           "  exact eLpNorm_sum_le_foo h\n"
           "  exact @eLpNorm_sum_le _ _ _ h\n"
           "  exact eLpNorm_le_eLpNorm_of_exponent_le (hf := hm) hpq\n")
    assert O.core_rewrites(src) == src


# renames: d13f23b's `Filter.eventuallyEqSet_univ` is our `Filter.eventuallyEq_univ`; its `eLpNorm_indicator_const`
# takes a NullMeasurableSet (every use), which is our `eLpNorm_indicator_const₀` (ours wants a MeasurableSet).

def test_eventually_eq_set_univ_and_indicator_const_renamed():
    src = ("    exact measure_congr (Filter.eventuallyEqSet_univ.mpr hη)\n"
           "    exact eventuallyEqSet_univ.mp (ae_eq_univ.mpr hc)\n"
           "    rw [eLpNorm_indicator_const hZ.nullMeasurableSet (by norm_num) (by norm_num)]\n"
           "  rw [he, eLpNorm_indicator_const (s := {x | N ≤ ρ x})\n")
    out = O.core_rewrites(src)
    assert out == ("    exact measure_congr (Filter.eventuallyEq_univ.mpr hη)\n"
                   "    exact eventuallyEq_univ.mp (ae_eq_univ.mpr hc)\n"
                   "    rw [eLpNorm_indicator_const₀ hZ.nullMeasurableSet (by norm_num) (by norm_num)]\n"
                   "  rw [he, eLpNorm_indicator_const₀ (s := {x | N ≤ ρ x})\n")
    keep = ("rw [eLpNorm_indicator_const₀ hs hp hp', eLpNorm_indicator_const' hs h hp, eLpNorm_indicator_const_le]\n"
            "exact Filter.eventuallyEqSet_univ_foo\n")
    assert O.core_rewrites(keep) == keep


# d13f23b's `mgf_gaussianReal` takes `HasLaw X (gaussianReal μ v) p`; ours takes its `map_eq` field,
# `p.map X = gaussianReal μ v` (oaiq-004, oaiq-036). An anonymous constructor keeps its second component; a named
# HasLaw proof gets `.map_eq`; `(by simp)` proves either and is kept.

def test_mgf_gaussian_real_takes_the_map_equation():
    src = ("  rw [mgf_gaussianReal ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩,\n"
           "  have H := mgf_gaussianReal\n"
           "    ⟨(innerSL ℝ v).continuous.measurable.aemeasurable,\n"
           "      IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)⟩ a\n"
           "  rw [mgf_gaussianReal (hB.hasLaw_eval t)]\n"
           "    rw [← mgf_pos_iff, mgf_gaussianReal hX]\n"
           "  have he := mgf_gaussianReal hl 1\n"
           "    have hh := mgf_gaussianReal (X := id) (p := gaussianReal 0 1) (by simp) (a i)\n"
           "  rw [mgf_gaussianReal (μ := 0) (v := v) (by simp)]\n"
           "  simp [mgf_gaussianReal]\n")
    out = O.core_rewrites(src)
    assert out == ("  rw [mgf_gaussianReal hX.map_eq_gaussianReal,\n"
                   "  have H := mgf_gaussianReal\n"
                   "    (IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)) a\n"
                   "  rw [mgf_gaussianReal (hB.hasLaw_eval t).map_eq]\n"
                   "    rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq]\n"
                   "  have he := mgf_gaussianReal hl.map_eq 1\n"
                   "    have hh := mgf_gaussianReal (X := id) (p := gaussianReal 0 1) (by simp) (a i)\n"
                   "  rw [mgf_gaussianReal (μ := 0) (v := v) (by simp)]\n"
                   "  simp [mgf_gaussianReal]\n")


# ---------------------------------------------------------------- inlined macros keep their definition-site names
# MatchingCount (oaiq-051, 2026-10-27): `macro "tree_cost"` is defined in `namespace OAI` under
# `open MatchingFPRAS.TreeTyped`, so its `apply polynomial_map` meant `TreeTyped.polynomial_map`. Inlined
# in `namespace MatchingFPRAS.ExecutableOptions` (which declares its own `polynomial_map`), the short name
# was captured, and `with_reducible repeat' (first | …)` silently left goals. The worker qualified 260
# sites by patch.

MC = 'OAI.Combinatorics.MatchingCount.'
MC_SOURCES = {
    MC + 'Complexity.TreePolynomialCollections': ('Complexity_TreePolynomialCollections', (
        'import Mathlib\n\nnamespace OAI\n\nnamespace MatchingFPRAS.TreeTyped\nopen Polynomial\n\n'
        'lemma polynomial_map {f : A → B} {F : Realizer f} (hF : PolynomialTime F) :\n'
        '    PolynomialTime (map F) := by\n  sorry\n\n'
        'lemma polynomial_add : PolynomialTime add := by\n  sorry\n\n'
        'end MatchingFPRAS.TreeTyped\n\nend OAI\n')),
    MC + 'Complexity.TreeCostTactic': ('Complexity_TreeCostTactic', (
        'import Mathlib\nimport OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialCollections\n\n'
        'namespace OAI\n\nopen MatchingFPRAS.TreeTyped\n\n'
        'macro "tree_cost" : tactic => `(tactic|\n'
        '  (with_reducible repeat\' (first\n    | assumption\n    | exact polynomial_add\n'
        '    | apply polynomial_map\n    | apply Nat.le_refl)))\n\nend OAI\n')),
    MC + 'Sampling.TreeOptions': ('Sampling_TreeOptions', (
        'import Mathlib\nimport OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic\n\n'
        'namespace OAI\n\nnamespace MatchingFPRAS.ExecutableOptions\nopen TreeTyped TreeFraction\n\n'
        'lemma polynomial_map {f : C×A→B} {F : Realizer f} (hF : PolynomialTime F) :\n'
        '    PolynomialTime (mapRealizer F) := by\n  tree_cost\n\n'
        'lemma polynomial_listSingleton : PolynomialTime listSingleton := by\n  tree_cost\n\n'
        'end MatchingFPRAS.ExecutableOptions\n\n'
        'lemma polynomial_other : PolynomialTime other := by\n  tree_cost\n\nend OAI\n')),
}


def test_inlined_macro_names_are_qualified_where_a_use_site_captures_them():
    out = O.inline_module_macros(MC_SOURCES)
    opts = out[MC + 'Sampling.TreeOptions'][1]
    assert 'tree_cost' not in opts
    q = 'apply OAI.MatchingFPRAS.TreeTyped.polynomial_map'
    assert opts.count(q) == 3                                     # every inlined copy, one text per port
    assert 'apply polynomial_map' not in opts
    # outside ExecutableOptions (and its `open TreeTyped`) the short `polynomial_add` names nothing: qualified too
    assert opts.count('exact OAI.MatchingFPRAS.TreeTyped.polynomial_add') == 3
    assert opts.count('apply Nat.le_refl') == 3                    # a Mathlib name is left alone
    assert 'assumption' in opts and 'with_reducible' in opts and 'OAI.first' not in opts
    # a name every use site resolves as the definition did keeps its short form (no churn for patches)
    src = dict(MC_SOURCES)
    k2 = MC + 'Sampling.TreeOptions'
    src[k2] = (src[k2][0], src[k2][1].split('lemma polynomial_other')[0] + 'end OAI\n')
    opts = O.inline_module_macros(src)[k2][1]
    assert opts.count('exact polynomial_add') == 2 and opts.count('TreeTyped.polynomial_map') == 2


def test_inlined_macro_name_without_a_definition_site_resolution_warns_on_capture():
    # `polynomial_listCons` is not declared where the macro is defined (a Mathlib or hypothesis name, as far
    # as the port can tell), but the use site's namespace declares one: no guess, a warning
    src = dict(MC_SOURCES)
    k = MC + 'Complexity.TreeCostTactic'
    src[k] = (src[k][0], src[k][1].replace('| apply Nat.le_refl', '| apply polynomial_listCons'))
    k2 = MC + 'Sampling.TreeOptions'
    src[k2] = (src[k2][0], src[k2][1].replace(
        'end MatchingFPRAS.ExecutableOptions', 'lemma polynomial_listCons : True := trivial\n\n'
        'end MatchingFPRAS.ExecutableOptions'))
    with pytest.warns(UserWarning, match=r'tree_cost.*polynomial_listCons.*ExecutableOptions'):
        out = O.inline_module_macros(src)
    assert 'apply polynomial_listCons' in out[k2][1]


def test_inlined_macro_names_qualify_with_root_when_the_full_name_is_shadowed():
    src = dict(MC_SOURCES)
    k2 = MC + 'Sampling.TreeOptions'
    src[k2] = (src[k2][0], src[k2][1].replace(
        'end MatchingFPRAS.ExecutableOptions', 'end MatchingFPRAS.ExecutableOptions\n\n'
        'namespace OAI.MatchingFPRAS.TreeTyped\nlemma polynomial_map : True := trivial\n'
        'end OAI.MatchingFPRAS.TreeTyped\n'))
    opts = O.inline_module_macros(src)[k2][1]
    assert opts.count('apply _root_.OAI.MatchingFPRAS.TreeTyped.polynomial_map') == 3


def test_macro_identifiers_skip_tactic_names_and_binders():
    # WLIdentification `word_poly`: `repeat' first | rfl | simp` — `first` is a tactic, though
    # `SchemaRealizer.first` is a ported declaration at a use site
    body = "repeat' first | rfl | simp [foo, Bar.baz] | (intro h; exact h.trans qux) | try apply quux 3"
    got = [x for _, _, x in O._macro_idents(body)]
    assert got == ['foo', 'Bar.baz', 'qux', 'quux']
