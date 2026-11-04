/-! # Part B: assumes `two_eq`, proves `four_eq` -/

namespace BP

/-- The same definition, its doc comment reworded. -/
def two : Nat :=
  2

-- ASSUMED FROM BLUEPRINT
theorem two_eq : two = 2 := sorry

end BP

namespace BP.PartB

theorem four_eq : BP.two + BP.two = 4 := by rw [BP.two_eq]

end BP.PartB
