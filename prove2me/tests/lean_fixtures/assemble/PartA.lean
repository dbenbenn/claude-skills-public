/-! # Part A: copies `two`, proves `two_eq` -/

namespace BP

/-- A definition. -/
def two : Nat := 2

end BP

namespace BP.PartA

theorem two_eq : BP.two = 2 := rfl

end BP.PartA

#print axioms BP.PartA.two_eq
