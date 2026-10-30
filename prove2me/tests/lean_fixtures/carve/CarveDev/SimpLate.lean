import CarveDev.SimpBase

namespace CD.Sp

@[simp] theorem h_eq (n : Nat) : h n = n := rfl

theorem late (n : Nat) : h n = n := by simp

end CD.Sp
