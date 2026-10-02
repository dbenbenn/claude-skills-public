import Mathlib

namespace M

/-- a copy, primed -/
theorem dep' (n : ℕ) : n + 0 = n := by
  simp

open Nat in
theorem dep'' (n : ℕ) : 0 + n = n := Nat.zero_add n

theorem stub : 1 = 1 := by sorry

theorem solution : True := trivial

end M
