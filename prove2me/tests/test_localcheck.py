"""p2mlib.localcheck: the pure parts of a local check that predicts the verifier (Erdős 3, 2026-10-16)."""
import pytest
from p2mlib import localcheck as L

SOL = """import Mathlib
import Definitions.Def_B1
import Theorems.Thm_Other

theorem foo_oai : True := trivial

theorem solution : type_of% @foo_oai := @foo_oai
"""
PRE = "import Mathlib\nimport Definitions.Def_B0\n"
FS = "theorem foo : True := by sorry\n"


def test_server_check_text_merges_imports_and_appends_the_check():
    t = L.server_check_text(SOL, PRE, FS, 'foo')
    head = [l for l in t.split('\n') if l.startswith('import ')]
    assert head == ['import Mathlib', 'import Definitions.Def_B1', 'import Theorems.Thm_Other',
                    'import Definitions.Def_B0', 'import Lean']
    assert t.index('theorem foo_oai') < t.index('theorem foo :') < t.index('theorem _check')
    assert 'theorem _check : type_of% @foo := @solution\n' in t
    assert t.index('theorem _check') < t.index('run_meta')     # then the coercion fallback
    # every import comes before any other text
    first_non_import = next(i for i, l in enumerate(t.split('\n')) if l and not l.startswith('import '))
    assert all(not l.startswith('import ') for l in t.split('\n')[first_non_import:])


def test_content_key_follows_imported_lib_files(tmp_path):
    lib = tmp_path / 'lib'; lib.mkdir()
    (lib / 'Def_B1.lean').write_text('def b := 1\n')
    sol = tmp_path / 'Sol.lean'; sol.write_text(SOL)
    k1 = L.content_key(str(sol), str(lib))
    assert k1 == L.content_key(str(sol), str(lib))
    (lib / 'Def_B1.lean').write_text('def b := 2\n')
    assert L.content_key(str(sol), str(lib)) != k1
    assert L.content_key(str(sol), str(lib), version='2') != L.content_key(str(sol), str(lib))


def test_server_check_text_runs_the_verifiers_coercion_fallback_for_a_polymorphic_target():
    # oaiq-039 (2026-10-28): on prove2.me a universe-polymorphic target is compared with `solution`
    # through a `CoeT solType x targetType` search, and 13 pieces whose search timed out got WA "failed to
    # synthesize CoeT ... (deterministic) timeout at `typeclass`" although `_check` compiles. Run the
    # same search in the local check: exactly those 13 of 246 polymorphic statements failed it.
    t = L.server_check_text(SOL, PRE, FS, 'foo')
    assert 'import Lean' in [l for l in t.split('\n') if l.startswith('import ')]
    tail = t[t.index('theorem _check'):]
    assert 'run_meta' in tail and '``CoeT' in tail and '`foo' in tail
    assert 'mkConstWithFreshMVarLevels `solution' in tail and 'synthInstance?' in tail
    assert 'levelParams.isEmpty' in tail          # a monomorphic target is compared directly
    assert L.COE_FAILURE in tail                  # the message carve_measure reports


def test_the_coercion_fallback_fails_on_a_stuck_universe_constraint():
    # oaiq-124 (2026-10-30): `boundary_edge_image_le`, with `{σ : Type (max us v)}` and an instance binder
    # `[Module.Free (MvPolynomial σ ℝ) …]`, got WA "stuck at solving universe constraint max ?u.5 ?u.11 =?=
    # max ?u.10 ?u.11 while trying to unify CoeT …"; locally `isDefEq` said true and left the constraint
    # postponed, so the check passed. Settle the postponed constraints as the elaborator does.
    tail = L.server_check_text(SOL, PRE, FS, 'foo')
    tail = tail[tail.index('theorem _check'):]
    assert 'processPostponed (mayPostpone := false)' in tail
    assert tail.index('isDefEq s t') < tail.index('processPostponed') < tail.index('synthInstance?')


def test_the_coercion_failure_reports_the_types_unshared_size_and_the_shortcut_remedy():
    # q129 (2026-10-30): the CoeT search fails on a statement compared with itself; what decides it is the
    # type's size as a tree (`Expr.sizeWithoutSharing`): `u * v = 1` on `unitary (Q τ ω)`, a RingCon
    # quotient, is 18.9M nodes and fails, 8.5M passes, and high-priority shortcut instances for the
    # carrier's classes bring it to 2,613 nodes and it passes. Say so in the message, rather than only
    # "fold it" (folding made FactorGeneration's pieces too slow for the verifier).
    tail = L.server_check_text(SOL, PRE, FS, 'foo')
    tail = tail[tail.index('theorem _check'):]
    assert 'sizeWithoutSharing' in tail
    assert 'shortcut instances' in tail
    assert L.COE_FAILURE in tail


MAX_STMT = """theorem %s {I : Type u} [Fintype I] {W : Type v} [Group W] {σ : Type (max us v)} [Fintype σ]
    {I' : Type u'} {W' : Type v'} (b : Module.Basis σ ℝ (I → ℝ)) (w : W') (i : I')
    [Module.Free (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)] :
    let D := MvPolynomial σ ℝ
    (⊥ : Submodule D D) ≤ ⊤ := %s
"""


@pytest.mark.lean
def test_a_max_only_universe_with_an_instance_binder_fails_the_local_check(tmp_path):
    from p2mlib import carve as C
    sol = ('import Mathlib\n\nuniverse u v us u\' v\'\n\n' + MAX_STMT % ('foo_oai', 'bot_le') +
           '\ntheorem solution.{a, b, c, d, e} : type_of% @foo_oai.{a, b, c, d, e} := @foo_oai.{a, b, c, d, e}\n')
    chk = tmp_path / 'Chk.lean'
    chk.write_text(L.server_check_text(sol, 'import Mathlib\n', MAX_STMT % ('foo', 'by sorry'), 'foo'))
    with pytest.raises(C.CarveError) as e:
        C.compile_file(str(chk), None, str(tmp_path / 'olean'))
    assert L.COE_FAILURE in str(e.value)
