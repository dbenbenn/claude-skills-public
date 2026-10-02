import Mathlib
import Definitions.Def_LodhaMooreWords

/-!
# Lemma 5.6 of Lodha–Moore fails when the commutation rule moves only positive letters

Lodha–Moore (arXiv:1308.4250v3) p. 9 list the substitution `y_u y_v ⇔ y_v y_u` (incompatible `u`,
`v`) without exponents, while the proof of Lemma 5.6 moves `y_{s10}⁻¹` past other letters. Here
`PosStep` is `LodhaMoore.Step` with the commutation rule restricted to positive exponents (which
contains the printed exponent-1 rule), every other rule unchanged (including the expansion of
`y_s⁻¹`). The standard form `W0 = y_00⁻¹ y_01⁻¹ y_1⁻¹ y_ε` derives no sufficiently expanded
standard form.

Proof (proofs/lemma56-literal/RESULT.md in the Lodha–Moore mission repo):
* semantics: `x_s`, `y_s` act on infinite binary sequences; a word acts on the right (`act`);
  every step preserves `act`;
* invariant (`Frozen`): the `y`-letters carry labels `(r, w, c)` from four expansion trees
  (roots `y_00⁻¹`, `y_01⁻¹`, `y_1⁻¹`, `y_ε`) in order (`Forest`), with exponent `c = ±1` and chart
  `η ↦ ψ_r (w η)` (`Good`); no two consecutive labels are positive and consecutive labels have
  different regions, so commutation, cancellation and merging of `y`-letters never apply;
* no frozen standard form is sufficiently expanded (the twist by `y` in the chart of `y_ε`'s
  descendants makes a required support a non-cone).
-/

open LodhaMoore

namespace LM56

/-! ## 1. The rules with positive commutation -/

/-- `LodhaMoore.Step` with `y_u^i y_v^j ⇔ y_v^j y_u^i` only for `i, j > 0`. -/
inductive PosStep : Word → Word → Prop
  | moveX (pre post : Word) (s t t' : Seq) (i : ℤ) (h : xFin s t = some t') :
      PosStep (pre ++ [(.y t, i), (.x s, 1)] ++ post) (pre ++ [(.x s, 1), (.y t', i)] ++ post)
  | moveXInv (pre post : Word) (s t t' : Seq) (i : ℤ) (h : xFinInv s t = some t') :
      PosStep (pre ++ [(.y t, i), (.x s, -1)] ++ post) (pre ++ [(.x s, -1), (.y t', i)] ++ post)
  | expand (pre post : Word) (s : Seq) :
      PosStep (pre ++ [(.y s, 1)] ++ post)
        (pre ++ [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
          (.y (s ++ [true, true]), 1)] ++ post)
  | expandInv (pre post : Word) (s : Seq) :
      PosStep (pre ++ [(.y s, -1)] ++ post)
        (pre ++ [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
          (.y (s ++ [true]), -1)] ++ post)
  | commute (pre post : Word) (u v : Seq) (i j : ℤ) (hi : 0 < i) (hj : 0 < j)
      (h : Incompatible u v) :
      PosStep (pre ++ [(.y u, i), (.y v, j)] ++ post) (pre ++ [(.y v, j), (.y u, i)] ++ post)
  | split (pre post : Word) (g : Gen) (i j : ℤ) (hi : i ≠ 0) (hj : j ≠ 0) (hij : 0 < i * j) :
      PosStep (pre ++ [(g, i + j)] ++ post) (pre ++ [(g, i), (g, j)] ++ post)
  | merge (pre post : Word) (g : Gen) (i j : ℤ) (hi : i ≠ 0) (hj : j ≠ 0) (hij : 0 < i * j) :
      PosStep (pre ++ [(g, i), (g, j)] ++ post) (pre ++ [(g, i + j)] ++ post)
  | cancel (pre post : Word) (s : Seq) (i : ℤ) (hi : i ≠ 0) :
      PosStep (pre ++ [(.y s, i), (.y s, -i)] ++ post) (pre ++ post)

/-- The start word `y_00⁻¹ y_01⁻¹ y_1⁻¹ y_ε`. -/
def W0 : Word := [(.y [false, false], -1), (.y [false, true], -1), (.y [true], -1), (.y [], 1)]

/-! ## 2. Semantics -/

abbrev Str := Stream' Bool

/-- The cone of sequences extending `u`. -/
def cone (u : Seq) : Set Str := Set.range (fun η : Str => u ++ₛ η)

/-- `x⁻¹`: `0η ↦ 00η`, `10η ↦ 01η`, `11η ↦ 1η`. -/
def xInvFun (ξ : Str) : Str :=
  match ξ 0, ξ 1 with
  | false, _ => [false, false] ++ₛ ξ.drop 1
  | true, false => [false, true] ++ₛ ξ.drop 2
  | true, true => [true] ++ₛ ξ.drop 2

theorem xInvFun_xFun (ξ : Str) : xInvFun (xFun ξ) = ξ := sorry
theorem xFun_xInvFun (ξ : Str) : xFun (xInvFun ξ) = ξ := sorry
theorem yFun_false_true (ξ : Str) : yFun false (yFun true ξ) = ξ := sorry
theorem yFun_true_false (ξ : Str) : yFun true (yFun false ξ) = ξ := sorry

/-- The recursion of `x` and `y^{±1}` (p. 5). -/
theorem xFun_00 (η : Str) : xFun ([false, false] ++ₛ η) = [false] ++ₛ η := sorry
theorem xFun_01 (η : Str) : xFun ([false, true] ++ₛ η) = [true, false] ++ₛ η := sorry
theorem xFun_1 (η : Str) : xFun ([true] ++ₛ η) = [true, true] ++ₛ η := sorry
theorem yFun_true_00 (η : Str) : yFun true ([false, false] ++ₛ η) = [false] ++ₛ yFun true η := sorry
theorem yFun_true_01 (η : Str) :
    yFun true ([false, true] ++ₛ η) = [true, false] ++ₛ yFun false η := sorry
theorem yFun_true_1 (η : Str) : yFun true ([true] ++ₛ η) = [true, true] ++ₛ yFun true η := sorry
theorem yFun_false_0 (η : Str) :
    yFun false ([false] ++ₛ η) = [false, false] ++ₛ yFun false η := sorry
theorem yFun_false_10 (η : Str) :
    yFun false ([true, false] ++ₛ η) = [false, true] ++ₛ yFun true η := sorry
theorem yFun_false_11 (η : Str) :
    yFun false ([true, true] ++ₛ η) = [true] ++ₛ yFun false η := sorry

theorem localize_append (s : Seq) (f : Str → Str) (η : Str) :
    localize s f (s ++ₛ η) = s ++ₛ f η := sorry
theorem localize_of_not_mem (s : Seq) (f : Str → Str) (ξ : Str) (h : ξ ∉ cone s) :
    localize s f ξ = ξ := sorry
theorem localize_symm (s : Seq) (p : Equiv.Perm Str) (ξ : Str) :
    localize s p.symm (localize s p ξ) = ξ := sorry

/-- `f` localized at `s`, as a permutation. -/
def locP (s : Seq) (p : Equiv.Perm Str) : Equiv.Perm Str where
  toFun := localize s p
  invFun := localize s p.symm
  left_inv := localize_symm s p
  right_inv := fun ξ => by simpa using localize_symm s p.symm ξ

/-- `x` as a permutation. -/
def xP : Equiv.Perm Str := ⟨xFun, xInvFun, xInvFun_xFun, xFun_xInvFun⟩

/-- `y` as a permutation. -/
def yP : Equiv.Perm Str := ⟨yFun true, yFun false, yFun_false_true, yFun_true_false⟩

/-- The permutation of a generator. -/
def genP : Gen → Equiv.Perm Str
  | .x s => locP s xP
  | .y s => locP s yP

/-- The right action of a word: `act (l :: w) = act w * l`, i.e. `ξ.(l w) = (ξ.l).w`. -/
def act : Word → Equiv.Perm Str
  | [] => 1
  | (g, n) :: w => act w * genP g ^ n

theorem act_append (u v : Word) : act (u ++ v) = act v * act u := sorry

/-- Every substitution preserves the value. -/
theorem act_posStep {V V' : Word} (h : PosStep V V') : act V = act V' := sorry

/-- `x_s` moves `t` to `t' = t.x_s` by prefix replacement. -/
theorem genP_x_of_xFin {s t t' : Seq} (h : xFin s t = some t') (η : Str) :
    genP (.x s) (t ++ₛ η) = t' ++ₛ η := sorry
/-- `x_s⁻¹` moves `t` to `t' = t.x_s⁻¹` by prefix replacement. -/
theorem genP_x_inv_of_xFinInv {s t t' : Seq} (h : xFinInv s t = some t') (η : Str) :
    (genP (.x s))⁻¹ (t ++ₛ η) = t' ++ₛ η := sorry
/-- `y_s^n` fixes the sequences outside `[s]`. -/
theorem genP_y_zpow_of_not_mem (s : Seq) (n : ℤ) (ξ : Str) (h : ξ ∉ cone s) :
    (genP (.y s) ^ n) ξ = ξ := sorry
/-- `y_s^n` maps `[s]` to itself. -/
theorem genP_y_zpow_mem_iff (s : Seq) (n : ℤ) (ξ : Str) :
    (genP (.y s) ^ n) ξ ∈ cone s ↔ ξ ∈ cone s := sorry

/-! ## 3. Labels, expansion trees and charts -/

/-- The roots: `y_00⁻¹`, `y_01⁻¹`, `y_1⁻¹`, `y_ε`. -/
inductive Root | A | B | C | D
  deriving DecidableEq

/-- The chart of a root: `η ↦ 00η`, `01η`, `1η`, and for `D` the inverse of the value of
`y_00⁻¹ y_01⁻¹ y_1⁻¹`. -/
def psi : Root → Str → Str
  | .A, η => [false, false] ++ₛ η
  | .B, η => [false, true] ++ₛ η
  | .C, η => [true] ++ₛ η
  | .D, η => (act (W0.take 3)).symm η

theorem psi_D_00 (ρ : Str) : psi .D ([false, false] ++ₛ ρ) = [false, false] ++ₛ yFun true ρ := sorry
theorem psi_D_01 (ρ : Str) : psi .D ([false, true] ++ₛ ρ) = [false, true] ++ₛ yFun true ρ := sorry
theorem psi_D_1 (ρ : Str) : psi .D ([true] ++ₛ ρ) = [true] ++ₛ yFun true ρ := sorry

/-- A label `(r, w, c)`: root, leaf, sign (`true` for exponent `1`). -/
abbrev Label := Root × Seq × Bool

/-- The region of a label: the image of `[w]` under the root chart. -/
def region (l : Label) : Set Str := psi l.1 '' cone l.2.1

/-- The leaves of the four expansion trees, in order: expanding a leaf of sign `c` replaces it in
place by its three children (signs `c, -c, c`). -/
inductive Forest : List Label → Prop
  | init : Forest [(.A, [], false), (.B, [], false), (.C, [], false), (.D, [], true)]
  | expandPos (L₁ L₂ : List Label) (r : Root) (w : Seq) :
      Forest (L₁ ++ [(r, w, true)] ++ L₂) →
      Forest (L₁ ++ [(r, w ++ [false, false], true), (r, w ++ [false, true], false),
        (r, w ++ [true], true)] ++ L₂)
  | expandNeg (L₁ L₂ : List Label) (r : Root) (w : Seq) :
      Forest (L₁ ++ [(r, w, false)] ++ L₂) →
      Forest (L₁ ++ [(r, w ++ [false], false), (r, w ++ [true, false], true),
        (r, w ++ [true, true], false)] ++ L₂)

/-- No two consecutive labels are positive. -/
theorem Forest.not_pos_pos {L : List Label} (hL : Forest L) (i : ℕ) (hi : i + 1 < L.length) :
    ¬ (L[i].2.2 = true ∧ L[i + 1].2.2 = true) := sorry

/-- Consecutive labels have different regions. -/
theorem Forest.region_ne {L : List Label} (hL : Forest L) (i : ℕ) (hi : i + 1 < L.length) :
    region L[i] ≠ region L[i + 1] := sorry

/-- `Good f V L`: reading `V` from the left with `f` the value of the prefix read so far, the
`y`-letters of `V` carry the labels `L` in order; the label `(r, w, c)` on `y_t^e` means
`e = 1` if `c` and `e = -1` otherwise, and `f (ψ_r (w η)) = t η` for all `η`. -/
def Good : Equiv.Perm Str → Word → List Label → Prop
  | _, [], L => L = []
  | f, (.x s, n) :: V, L => Good (genP (.x s) ^ n * f) V L
  | _, (.y _, _) :: _, [] => False
  | f, (.y t, e) :: V, (r, w, c) :: L =>
      e = (if c then 1 else -1) ∧ (∀ η, f (psi r (w ++ₛ η)) = t ++ₛ η) ∧
        Good (genP (.y t) ^ e * f) V L

/-- Splitting `Good` along a concatenation. -/
theorem good_append (f : Equiv.Perm Str) (U V : Word) (L : List Label) :
    Good f (U ++ V) L ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ Good f U L₁ ∧ Good (act U * f) V L₂ := sorry

/-- The invariant. -/
def Frozen (V : Word) : Prop := ∃ L, Forest L ∧ Good 1 V L

theorem frozen_W0 : Frozen W0 := sorry

theorem frozen_posStep {V V' : Word} (hV : Frozen V) (h : PosStep V V') : Frozen V' := sorry

/-! ## 4. No frozen standard form is sufficiently expanded -/

theorem isStandardForm_W0 : IsStandardForm W0 := sorry

theorem not_sufficientlyExpanded_of_frozen {V : Word} (hV : Frozen V) (hS : IsStandardForm V) :
    ¬ SufficientlyExpanded V := sorry

/-! ## 5. Lemma 5.6 fails -/

theorem frozen_of_derives {V : Word} (h : Relation.ReflTransGen PosStep W0 V) : Frozen V := by
  induction h with
  | refl => exact frozen_W0
  | tail _ hst ih => exact frozen_posStep ih hst

theorem lemma56_fails :
    ¬ ∀ W, IsStandardForm W → ∃ W', Relation.ReflTransGen PosStep W W' ∧ IsStandardForm W' ∧
      SufficientlyExpanded W' := by
  intro h
  obtain ⟨W', hd, hs, hse⟩ := h W0 isStandardForm_W0
  exact not_sufficientlyExpanded_of_frozen (frozen_of_derives hd) hs hse

end LM56
