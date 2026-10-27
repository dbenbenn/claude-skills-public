/-! # CarveDev.InstColA / InstColB: local instances a carved file must bring back

* Lech multiplicity (oaiq-032, 2026-10-27): ten modules each declare `private local instance
  concreteRing`, `baseAlgebra`, … under the same names (collision renames `_pN`). A file keeping one
  module's copy took every other module's copy for kept too, so a declaration needing another
  module's copy lost it; and a re-emitted `baseAlgebra_r…` came before the `concreteRing` its own
  statement needs ("typeclass instance problem is stuck"). `oneR`'s statement needs `zeroR`.
* Thomason (oaiq-043, 2026-10-27): `local instance : LinearOrder (OrdinalVertices n)` and
  `local instance : Fintype (OrdinalVertices n)` on a type synonym; the Fintype one's uses left no
  record, so it was carved away while its LinearOrder sibling stayed (`Verts` here). -/

namespace CD.IC

structure R (n : Nat) where
  x : Nat

class Zeroish (α : Type) where
  z : α

class Oneish (α : Type) [Zeroish α] where
  o : α

private local instance zeroR (n : Nat) : Zeroish (R n) := ⟨⟨0⟩⟩
private local instance oneR (n : Nat) : Oneish (R n) := ⟨⟨1⟩⟩

theorem one_a (n : Nat) : (Oneish.o : R n).x = 1 := rfl

def Verts (n : Nat) : Type := R n

local instance (n : Nat) : Zeroish (Verts n) := ⟨⟨0⟩⟩
local instance (n : Nat) : Inhabited (Verts n) := ⟨⟨5⟩⟩

theorem verts_zero (n : Nat) : (Zeroish.z : Verts n).x = 0 := rfl

end CD.IC
