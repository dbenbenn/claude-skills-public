/-! # CarveDev.ExpImpl: the declarations ExpOnly exports under another namespace -/

namespace CD.EX.Impl

def val (n : Nat) : Nat := n + 2

theorem val_eq (n : Nat) : val n = n + 2 := rfl

end CD.EX.Impl
