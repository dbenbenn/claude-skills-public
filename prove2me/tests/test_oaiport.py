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
           "exact Measure.map_smul c μ f\n")
    out = O.core_rewrites(src)
    assert "rw [Measure.map_smul,map_add_right_eq_self]" in out
    assert "rw [Measure.map_smul,hrestr]" in out
    assert "rw [Measure.map_smul]\n" in out
    assert "exact Measure.map_smul c μ f" in out


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
