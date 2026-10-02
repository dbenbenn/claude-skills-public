import Mathlib

namespace Dev

/-- A local predicate standing for part of a published statement. -/
def Moves (f : ℝ ≃o ℝ) (x : ℝ) : Prop := f x ≠ x

-- HomeoLine.zpow_moves_of_moves, through `Moves`, with explicit binders and other names
theorem my_zpow (g : ℝ ≃o ℝ) (y : ℝ) (hy : Moves g y) : ∀ n : ℤ, n ≠ 0 → Moves (g ^ n) y := by
  sorry

-- BlockCycleRotation.fib_two_le with an explicit binder
theorem fib_copy (j : ℕ) : 2 ≤ Nat.fib (j + 3) := by
  sorry

-- a special case of BlockCycleRotation.gcd_min_eq is not the same statement
theorem gcd_decoy : Nat.gcd 6 (min 2 (6 - 2)) = Nat.gcd 6 2 := by
  decide

end Dev
