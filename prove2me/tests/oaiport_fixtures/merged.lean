universe u w

namespace OAI

namespace Glob

/-- OpenAI's copy of the bundle's structure. -/
structure Hom where
  f : Nat

namespace Hom
def id : Hom := ⟨0⟩
-- OpenAI's own Hom.comp: not in the bundle, kept
def comp (a b : Hom) : Hom := ⟨a.f + b.f⟩
end Hom

def Row (d : Nat) : Type := Fin d → Nat

instance : Inhabited (Row d) := ⟨fun _ => 0⟩

-- a different anonymous instance: kept
instance : Nonempty (Row 0) := ⟨fun x => x.elim0⟩

instance (priority := 100) rowNonempty : Nonempty (Row d) := ⟨fun _ => 0⟩

local instance scopedInst : Inhabited Hom := ⟨⟨1⟩⟩

def _root_.rootLevelThing : Nat := 3

attribute [-simp] Nat.add_comm in
omit u in
theorem stated.{w} (α : Sort w) : True := trivial

open Nat in
theorem keptAfterModifier : True := trivial

end Glob

namespace Other
-- same last components as the bundle's Hom.id, in another namespace: kept
structure Hom where
  g : Nat
def Hom.id : Hom := ⟨0⟩
end Other

end OAI
