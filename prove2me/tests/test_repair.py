"""p2mlib.repair: cutting a context command Lean rejects from a carved file."""
from p2mlib import repair as R

FILE = '''import Mathlib

section
namespace OAI

variable {m : ℕ} (J : Fin m → Type*)
  [∀ j, Fintype (J j)]

local notation "G" => EnlargedKernel m J

open Foo Bar

/-- A definition. -/
def keep (n : ℕ) : ℕ :=
  n + 1

theorem keep_eq : keep 0 = 1 := by
  rfl

end OAI
end
'''


def err(line, col=0, msg='error: boom'):
    return 'Def_X.lean:%d:%d: %s' % (line, col, msg)


def test_errors_are_read_from_compiler_output():
    out = ('Def_X.lean:9:31: error: Unknown identifier `m` at quotation precheck\n'
           'Def_X.lean:9:31: warning: unused\nnoise\n/abs/Def_X.lean:14:2: error(lean.x): bad\n')
    assert R.error_lines(out) == [9, 14]


def test_a_failing_local_notation_is_cut():
    new, cut = R.repair(FILE, [err(9, 31)])
    assert 'local notation "G"' not in new and cut == ['local notation "G" => EnlargedKernel m J']
    assert 'def keep' in new and 'variable {m : ℕ}' in new


def test_a_multiline_variable_is_cut_whole():
    new, cut = R.repair(FILE, [err(7, 4)])                    # the continuation line
    assert 'variable {m' not in new and '[∀ j, Fintype (J j)]' not in new
    assert cut[0].startswith('variable {m : ℕ}') and cut[0].endswith('[∀ j, Fintype (J j)]')


def test_an_error_inside_a_declaration_is_not_repaired():
    assert R.repair(FILE, [err(15, 2)]) is None               # in `def keep`'s body
    assert R.repair(FILE, [err(9, 1), err(18, 2)]) is None    # any genuine error: no repair at all


def test_scoped_notation_is_never_cut():
    f = FILE.replace('local notation "G"', 'scoped[S] notation "G"')
    assert R.repair(f, [err(9, 3)]) is None


def test_open_include_omit_and_local_attributes_are_context():
    for cmd in ('open Foo Bar', 'include hx', 'omit hx', 'attribute [local instance] foo',
                'open scoped Foo', 'local notation3 "X" => y'):
        f = FILE.replace('open Foo Bar', cmd)
        new, cut = R.repair(f, [err(11, 1)])
        assert cut == [cmd] and cmd not in new


def test_recorded_cuts_reapply_only_where_their_text_still_is():
    cuts = ['local notation "G" => EnlargedKernel m J', 'variable (gone : ℕ)']
    new, applied, stale = R.apply_cuts(FILE, cuts)
    assert 'local notation "G"' not in new
    assert applied == [cuts[0]] and stale == [cuts[1]]
    again, applied2, _ = R.apply_cuts(new, cuts)
    assert again == new and applied2 == []                    # idempotent
