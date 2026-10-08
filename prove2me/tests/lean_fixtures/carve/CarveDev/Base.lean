/-! # CarveDev.Base: the definitions (this file deliberately ends without a newline) -/

universe u

namespace CD

/-- The identity, universe-polymorphic. -/
def pick {α : Sort u} (a : α) : α := a

/-- A pointed type. -/
structure Space where
  carrier : Type
  pt : carrier

/-- The size of a space (always zero). -/
def Space.size (_A : Space) : Nat := 0
@[simp] theorem Space.size_eq (A : Space) : A.size = 0 := rfl

def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = n + n := rfl

def unusedDef : Nat := 3

theorem unused_thm : unusedDef = 3 := rfl

/-- A port's stubbed proof (Erdős 3 B022: a bundle kept a declaration using `sorry`). -/
theorem sorried : double 2 = 4 := sorry

def usesSorried : Nat := (fun (_ : double 2 = 4) => 0) sorried

example : double 1 = 2 := rfl

end CD

namespace CD.Aux

def auxOnly : Nat := 1

local notation "AUX" => auxOnly

attribute [reducible] auxOnly

theorem aux_eq : AUX = 1 := rfl

end CD.Aux