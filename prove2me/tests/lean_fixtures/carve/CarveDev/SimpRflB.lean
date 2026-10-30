import CarveDev.SimpRflA

namespace CD.SR

theorem useF (n : Nat) : f n = n + 1 := by
  simp

theorem useF_only (n : Nat) : f n = n + 1 := by
  simp only [f]

end CD.SR
