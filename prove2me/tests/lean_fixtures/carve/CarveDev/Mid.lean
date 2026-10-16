import CarveDev.Base

universe u

namespace CD

theorem pick_eq {α : Sort u} (a : α) : pick a = a := rfl

/-- A coordinate of a space. -/
def Space.coord (_A : Space) : Nat := 0

theorem Space.coord_eq (A : Space) : A.coord = 0 := rfl

/-- `A.coord_eq` is named only in the source, through the local `A`'s dot notation, and `dsimp`
leaves no trace of it in the term (Erdős 3 B024, "Unknown identifier `coord`"). -/
theorem size_via_coord (A : Space) : A.coord + A.size = 0 := by
  dsimp only [A.coord_eq]
  simp

/-- Four times, a definition of this module (so Mid has bundle material of its own). -/
def quad (n : Nat) : Nat := double (double n)

open List

local notation "DE" => double_eq

/-- Double zero, through the notation. -/
theorem double_zero : double 0 = 0 := DE 0

private theorem helper : True := trivial

variable (A : Space)
  (n : Nat)
  (hx : Aux.auxOnly = 1)

include hx

theorem uses_hx : Aux.auxOnly = 1 := hx

omit
  hx in
theorem size_zero : A.size = 0 := by simp

omit hx in
theorem double_succ : double (n + 1) = double n + 2 := by
  have := helper
  simp only [double_eq]; omega

#check double_succ

/-- A definition whose embedded proof uses the rfl simp lemma `Space.size_eq` with no trace in the
term (the schedule chunker must still put that lemma where this definition's bundle sees it). -/
def sizedZero (B : Space) : {n : Nat // n = B.size} := ⟨0, by simp⟩

section
open scoped CDScope
def viaScoped (n : Nat) : Nat := ⟪n⟫
end

namespace Space
variable (S : Space)
variable (hS : S.big)
/-- Uses no variable: a carved file without `Space.big` must drop `hS`'s group, whose type is
field notation on the variable `S`, inside a namespace that is itself a declaration (Erdős 3 v2 B109: `variable (hT : T.UnitIntervalValued)`). -/
theorem field_free (k : Nat) : k = k := rfl
end Space

section UnusedNote
variable (w : Wide)
local notation "WZ" => w
/-- Uses neither `w` nor `WZ`: the unused notation must not keep `w`'s group alive (Erdős 3 v2
stub: `local notation "hamin" => … B` kept `variable (B : LayerSamplerAxis I n → Type*)`). -/
theorem note_free (k : Nat) : k + 0 = k := rfl
end UnusedNote

namespace Nat
/-- A project namespace with the name of Lean's `Nat`. -/
def cdTwice (n : Nat) : Nat := n + n
end Nat

section Trailing
variable (q : Nat)
def trail_kept : Nat := q
variable [Inhabited Wide]
/-- Nothing kept follows the second `variable`: it goes (Erdős 3 v2 B038, a trailing
`variable [∀ j, IsZLattice …]` whose instance no kept declaration brought in). -/
theorem trail_dropped : (1 : Nat) = 1 := rfl
end Trailing

namespace Space
variable (F : Nat → Space)
variable (hF : ∀ k, (F k).big)
/-- The field after a parenthesized application names CD.Space.big too (Erdős 3 v2 B065,
`variable (h : ∀ a, (e a).Bounds …)`). -/
theorem paren_free (k : Nat) : k = k := rfl
end Space

end CD
