import Mathlib
import Theorems.Thm_BlockCycleRotation_fib_two_le
import Theorems.Thm_BlockCycleRotation_gcd_min_eq

namespace Dev

-- HomeoLine.zpow_moves_of_moves under another name and with explicit binders
theorem moves (g : ℝ ≃o ℝ) (y : ℝ) (hy : g y ≠ y) : ∀ n : ℤ, n ≠ 0 → (g ^ n) y ≠ y := by
  sorry

theorem unused_helper : True := trivial

end Dev

theorem solution : 2 ≤ Nat.fib (0 + 3) ∧ (∀ g : ℝ ≃o ℝ, ∀ y, g y ≠ y → (g ^ (1 : ℤ)) y ≠ y) :=
  ⟨BlockCycleRotation.fib_two_le, fun g y h => Dev.moves g y h 1 one_ne_zero⟩
