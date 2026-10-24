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


def test_core_rewrites_add_the_zero_case_of_tensor_induction():
    src = '  induction x using TensorProduct.inductionOn with\n  | tmul a b => simp\n'
    out = O.core_rewrites(src)
    assert 'TensorProduct.induction_on with\n  | zero => simp only [map_zero]\n  | tmul' in out


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
