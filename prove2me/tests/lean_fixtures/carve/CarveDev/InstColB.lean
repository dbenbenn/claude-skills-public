import CarveDev.InstColA

namespace CD.IC

private local instance zeroR (n : Nat) : Zeroish (R n) := ⟨⟨0⟩⟩
private local instance oneR (n : Nat) : Oneish (R n) := ⟨⟨2⟩⟩

theorem one_b (n : Nat) : (Oneish.o : R n).x = 2 := rfl

end CD.IC
