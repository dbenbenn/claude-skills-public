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

section UsedVars
variable (k0 : Nat) (hq : double 0 = 0)
variable (hk : double k0 = k0)
/-- Lean includes neither `hq` nor `hk` here: the compiled declaration mentions no `double`, so a
carved file drops both groups (Erdős 3 v2 B066: `variable [∀ j, IsZLattice ℝ (latticeSection …)]`
before a definition that does not use it, needing an instance nothing kept brought in). -/
def unused_var_free : Nat := 7
include hk in
/-- Uses `hk`: its group stays. -/
theorem uses_hk : double k0 = k0 := hk
variable (k1 : Nat) (hk1 : k1.succ = k1 + 1)
include hk1 in
/-- `k1.succ` is `Nat.succ`, not the project's `Wide.succ`: the group stays (Erdős 3 v2 B107,
`(hF' : … (b.reindex e) …)` dropped because a project declaration is also called `reindex`). -/
theorem uses_hk1 : k1.succ = k1 + 1 := hk1
variable (hk2 : (k1 + 1).pred = k1)
include hk2 in
/-- `.pred` after a parenthesis is `Nat.pred`, a field, not the project's `CD.pred` (Erdős 3 v2
B167, `(…).map` read as the project's `VectorPolynomial.map`). -/
theorem uses_hk2 : (k1 + 1).pred = k1 := hk2
end UsedVars

/-- Declared as `Space.…`, so its body reads `size_eq` as `Space.size_eq`; the simp lemma leaves no
trace in the term (Erdős 3 v2 B188: `simp only [tensorPower_eval]` in
`NativeMultidegreeNilcharacter.mixedPermutationProduct_tensorPower`, bundle not imported). -/
theorem Space.cd_unused_simp : True := by
  simp only [size_eq]

/-- Uses a theorem by dot notation, as a name and after a parenthesis: a carved file renaming
`Space.coord_eq` must rename both (Erdős 3 v2: `D.localize` and `(…).relativePatchSliceConclusion_…`
kept their old names, "Invalid field"). -/
theorem uses_dot_thm (A : Space) : A.coord = 0 ∧ A.coord = 0 := ⟨A.coord_eq, (id A).coord_eq⟩

section PermOpen
open _root_.List Perm
/-- `Perm` opens the project's `CD.Perm` and, through the `open _root_.List` just before it, Lean's
`List.Perm`, whose `length_eq` this uses: a carved file without `CD.Perm` must keep the reading
(Kaplansky 2026-10-18: ReducedWalks' `open _root_.SimpleGraph _root_.OAI.SimpleGraph Walk` lost
`Walk`, "Unknown identifier `length_eq_zero_iff`"). -/
theorem perm_length_cd (l l' : List Nat) (h : l.Perm l') : l.length = l'.length := length_eq h
end PermOpen

/-- Uses Lean's `Nat.succ_le_succ` while the project has a `CD.Pkg.succ_le_succ`: renaming the
project's one must leave Lean's alone (Kaplansky 2026-10-18: the `_oai` rename of
`MultipleHNN.of_injective` turned `HNNExtension.of_injective` into `HNNExtension.of_injective_oai`). -/
theorem uses_core_succ (n m : Nat) (h : n ≤ m) : n.succ ≤ m.succ := Nat.succ_le_succ h

/-- A definition whose value uses a theorem: forced, `double_eq` is published as a statement and
this definition's bundle imports it (prove2.me's /submit-definition may import `Theorems.Thm_…`;
UniversalFInfinity's `Milnor.ghostMap` rests on cellular approximation this way). -/
def doubleWitness (n : Nat) : {m : Nat // m = n + n} := ⟨double n, double_eq n⟩

theorem uses_witness : (doubleWitness 1).val = 2 := rfl

end CD
