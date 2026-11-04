namespace BP

def two : Nat := 2

-- ASSUMED FROM BLUEPRINT
theorem two_eq : two = 1 + 1 := sorry

end BP

namespace BP.PartBadStub

theorem four_eq : BP.two + BP.two = 4 := by rw [BP.two_eq]

end BP.PartBadStub
