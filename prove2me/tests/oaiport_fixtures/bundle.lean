import Mathlib

namespace OAI

namespace Glob

structure Hom where
  f : Nat

namespace Hom
def id : Hom := ⟨0⟩
end Hom

def Row (d : Nat) : Type := Fin d → Nat

instance : Inhabited (Row d) := ⟨fun _ => 0⟩

instance (priority := 100) rowNonempty : Nonempty (Row d) := ⟨fun _ => 0⟩

scoped instance scopedInst : Inhabited Hom := ⟨⟨1⟩⟩

def _root_.rootLevelThing : Nat := 3

theorem stated.{w} (α : Sort w) : True := trivial

end Glob

end OAI
