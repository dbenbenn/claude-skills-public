import Mathlib

namespace Sc

theorem helper_eq (n : ℕ) : n + 0 = n := rfl

section
attribute [local simp] helper_eq

theorem uses (n : ℕ) : n + 0 = n := by simp

end

def HB : Prop := True

section
variable (hb : HB)
include hb

theorem needs_hb : True := trivial

end

end Sc

theorem solution : True := trivial
