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
