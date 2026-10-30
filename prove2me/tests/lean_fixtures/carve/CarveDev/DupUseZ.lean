import CarveDev.DupZ

namespace CD.Dup

theorem useZ (n : Nat) : n ≤ n + 1 := bound n

theorem useZ' (n : Nat) : n + 1 ≤ n + 1 + 1 := CD.Dup.bound (n + 1)

end CD.Dup
