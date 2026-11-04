namespace BP

def two : Nat := 2

-- ASSUMED, but not from this Blueprint
theorem two_pos : 0 < two := sorry

end BP

namespace BP.PartBadAssume

theorem four_eq : BP.two + BP.two = 4 := rfl

end BP.PartBadAssume
