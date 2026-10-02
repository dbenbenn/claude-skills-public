import Mathlib

open scoped ENNReal

notation "bump " x => x + 1

noncomputable def g : ℝ≥0∞ := 1

theorem g_le : g ≤ g := le_refl _

theorem n1 : (bump (1 : ℕ)) = 2 := rfl
