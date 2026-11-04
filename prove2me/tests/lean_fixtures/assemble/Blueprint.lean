/-! # A copy-header Blueprint (assemble_blueprint fixture) -/

namespace BP

/-- A definition. -/
def two : Nat := 2

theorem two_eq : two = 2 := by
  sorry

theorem four_eq : two + two = 4 := by
  sorry

theorem top (n : Nat) (h : n = 0) : two + two + n = 4 := by
  rw [h, Nat.add_zero, four_eq]

end BP
