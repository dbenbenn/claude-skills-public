/-! # Part: proves `two_eq` under its own name, restated differently -/

namespace BP

def two : Nat := 2

theorem two_eq : two = 1 + 1 := rfl

end BP
