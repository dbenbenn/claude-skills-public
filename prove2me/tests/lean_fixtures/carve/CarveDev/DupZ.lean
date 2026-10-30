/-! # CarveDev.DupZ: the other copy of DupA's `CD.Dup.bound`, with its own proof -/

namespace CD.Dup

theorem bound (n : Nat) : n ≤ n + 1 := Nat.le_add_right n 1

end CD.Dup
