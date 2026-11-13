/-! # CarveDev.InstPre: a re-declared local instance and the instances it is built from

Duke MainUnconditional (q362, 2026-11-13): a section declared `local instance …FiniteDimensional ℚ B
:= FiniteDimensional.trans ℚ A B`, whose two `FiniteDimensional` arguments instance synthesis found
among the section's earlier local instances. A bundle keeping a declaration of the section re-declared
it (`…_r10b556_1`), but not those two, which name a theorem the bundle lacks: "failed to synthesize".
Here `fdPairFin1` is built by `Fin1.up` from `fdFin1`, which names the theorem `fin1_fd`;
`pair_default` uses only `fdPairInh`, on the same carrier, which brings the others back with it. -/

namespace CD.IP

structure Fd (n : Nat) where
  x : Nat

class Fin1 (α : Type) : Prop where
  ok : True

theorem Fin1.up (α β : Type) [Fin1 α] : Fin1 (α × β) := ⟨trivial⟩

theorem fin1_fd (n : Nat) : Fin1 (Fd n) := ⟨trivial⟩

section

local instance fdFin1 (n : Nat) : Fin1 (Fd n) := fin1_fd n

local instance fdPairFin1 (n : Nat) : Fin1 (Fd n × Nat) := Fin1.up (Fd n) Nat

local instance fdPairInh (n : Nat) : Inhabited (Fd n × Nat) := ⟨(⟨1⟩, 0)⟩

theorem pair_default (n : Nat) : (default : Fd n × Nat).2 = 0 := rfl

end

end CD.IP
