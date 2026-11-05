/-! # Part: proves `two_eq` under the Blueprint's own name (q195) -/

namespace BP

def two : Nat := 2

theorem two_eq : two = 2 := rfl

end BP
