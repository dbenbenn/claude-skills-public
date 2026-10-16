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

/-- A predicate reached by field notation on a variable (`variable (hS : S.big)`). -/
def Space.big (B : Space) : Prop := B.size = 0

/-- A type only a variable mentions. -/
structure Wide where
  w : Nat

section
open Nat
/-- `open Nat` means Lean's `Nat` here; the project's `CD.Nat` (declared in Mid) does not exist yet,
but a file this statement is appended to may have it (Erdős 3 v2: `open MvPolynomial` read as
`OAI.Erdos3.MvPolynomial` after the solution, "Unknown identifier `eval`"). -/
theorem succ_pos_cd (n : Nat) : 0 < succ n := Nat.succ_pos n
end

end CD

namespace CD.Aux

def auxOnly : Nat := 1

local notation "AUX" => auxOnly

attribute [reducible] auxOnly

theorem aux_eq : AUX = 1 := rfl

end CD.Aux

/- A scoped notation: its namespace exists only once this module's text is in force, so whatever
opens it must see the bundle that carries the notation (Erdős 3 v2: `open scoped Indicator`). -/
namespace CDScope
scoped notation "⟪" x "⟫" => CD.double x
/-- The first declaration after the notation in its scope: the notation travels with it. -/
def anchor : Nat := 0
end CDScope
