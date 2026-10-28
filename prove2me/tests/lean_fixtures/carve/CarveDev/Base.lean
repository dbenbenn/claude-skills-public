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

/-- A project declaration named like a field of `Nat` (`(k + 1).pred`). -/
def pred (n : Nat) : Nat := n

/-- A project declaration whose short name is also a field of `Nat` (`k.succ`). -/
def Wide.succ (x : Wide) : Wide := x

section
open Nat
/-- `open Nat` means Lean's `Nat` here; the project's `CD.Nat` (declared in Mid) does not exist yet,
but a file this statement is appended to may have it (Erdős 3 v2: `open MvPolynomial` read as
`OAI.Erdos3.MvPolynomial` after the solution, "Unknown identifier `eval`"). -/
theorem succ_pos_cd (n : Nat) : 0 < succ n := Nat.succ_pos n
end

section
open Int
/-- `open Int` meant Lean's `Int`: the project's `CD.Int` is only created further down this file,
so a carved file where it comes first must say `_root_.Int` (Erdős 3 v2 B172, `open MvPolynomial`
before the module's own `namespace OAI.MvPolynomial`, "Unknown identifier `eval`"). -/
theorem natAbs_cd (a : Int) : natAbs a = Int.natAbs a := rfl
end

namespace Int
/-- The project namespace created after the `open`. -/
def cdId (a : _root_.Int) : _root_.Int := a
end Int

section
/-- A named local instance (Erdős 3 v2: `local instance forecastModulusNeZero (Pr) (A) : NeZero …`,
which a carved statement needs to make `ZMod (∏ …)` finite, and which no bundle carries). -/
local instance cdLocalInst : Inhabited Wide := ⟨⟨0⟩⟩
theorem uses_local_inst : (default : Wide).w = 0 := rfl
/-- In the local instance's scope but never uses it: a carved file keeping only this does not need
the instance (the carver used to re-emit every local instance in scope). -/
theorem no_inst_use : (1 : Nat) = 1 := rfl
/- A binder that needs the local instance to elaborate: the instance must come back before the
`variable`, not only before the theorem (Erdős 3 v2: `variable (hread : … W.cover …)` after
`local instance … : NeZero W.cover`). -/
variable (hdef : (default : Wide).w = 0)
include hdef in
theorem uses_hdef : (default : Wide).w = 0 := hdef
end

section
local notation "WD" => (⟨0⟩ : Wide)
/- The notation is used only by the local instance, which a carved file re-emits: the notation must
stay (Erdős 3 v2: `local instance … : NeZero Ncrt` re-emitted, `local notation "Ncrt"` dropped). -/
local instance cdLocalInst2 : Inhabited Wide := ⟨WD⟩
variable (hdef2 : (default : Wide).w = 0)
include hdef2 in
theorem uses_hdef2 : (default : Wide).w = 0 := hdef2
end

end CD

/- A project namespace whose last component is also a namespace of Lean's (`List.Perm`), and a
theorem whose short name is also one of Lean's (`Nat.succ_le_succ`). -/
namespace CD.Perm
def cdPerm : Nat := 3
end CD.Perm

namespace CD.Pkg
theorem succ_le_succ (n : Nat) : n ≤ n.succ := Nat.le_succ n
end CD.Pkg

namespace CD.Aux

def auxOnly : Nat := 1

local notation "AUX" => auxOnly

attribute [reducible] auxOnly

theorem aux_eq : AUX = 1 := rfl

end CD.Aux

/- PeriodicLattice (oaiq-067): a module's own `@[simp]` rfl lemma about library constants only,
used by a later `simp` through the default simp set: dsimp-style, so no term names it, and no
constant of its statement is the project's. -/
namespace CD
@[simp] theorem lcm23 : Nat.lcm 2 3 = 6 := rfl

theorem uses_lcm23 (n : Nat) : n + Nat.lcm 2 3 = n + 6 := by simp

theorem uses_lcm23_only (n : Nat) : n + 0 = n := by simp only [Nat.add_zero]
end CD

/- A scoped notation: its namespace exists only once this module's text is in force, so whatever
opens it must see the bundle that carries the notation (Erdős 3 v2: `open scoped Indicator`). -/
namespace CDScope
scoped notation "⟪" x "⟫" => CD.double x
/-- The first declaration after the notation in its scope: the notation travels with it. -/
def anchor : Nat := 0
end CDScope
