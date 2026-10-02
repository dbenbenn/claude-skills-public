import Solutions.LM56.Blueprint

open LodhaMoore LM56

namespace LM56.PartG

/-! ## Unfolding `Good` -/

theorem good_nil' (f : Equiv.Perm Str) (L : List Label) : Good f [] L ↔ L = [] := by
  simp [Good]

theorem good_x' (f : Equiv.Perm Str) (s : Seq) (n : ℤ) (V : Word) (L : List Label) :
    Good f ((.x s, n) :: V) L ↔ Good (genP (.x s) ^ n * f) V L := by
  simp [Good]

theorem good_y' (f : Equiv.Perm Str) (t : Seq) (e : ℤ) (V : Word) (L : List Label) :
    Good f ((.y t, e) :: V) L ↔ ∃ r w c L', L = (r, w, c) :: L' ∧ e = (if c then 1 else -1) ∧
      (∀ η, f (psi r (w ++ₛ η)) = t ++ₛ η) ∧ Good (genP (.y t) ^ e * f) V L' := by
  rcases L with _ | ⟨⟨r, w, c⟩, L'⟩
  · simp [Good]
  · simp only [Good]
    constructor
    · rintro ⟨he, hc, h⟩
      exact ⟨r, w, c, L', rfl, he, hc, h⟩
    · rintro ⟨r', w', c', L'', h, he, hc, hg⟩
      simp only [List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      exact ⟨he, hc, hg⟩

theorem good_append (f : Equiv.Perm Str) (U V : Word) (L : List Label) :
    Good f (U ++ V) L ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ Good f U L₁ ∧ Good (act U * f) V L₂ := by
  induction U generalizing f L with
  | nil => simp [good_nil', act]
  | cons a U ih =>
    obtain ⟨g, n⟩ := a
    cases g with
    | x s =>
      simp only [List.cons_append, good_x', ih, act, mul_assoc]
    | y t =>
      simp only [List.cons_append, good_y', ih, act, mul_assoc]
      constructor
      · rintro ⟨r, w, c, L', rfl, he, hc, L₁, L₂, rfl, h1, h2⟩
        exact ⟨(r, w, c) :: L₁, L₂, rfl, ⟨r, w, c, L₁, rfl, he, hc, h1⟩, h2⟩
      · rintro ⟨L₁, L₂, rfl, ⟨r, w, c, L₁', rfl, he, hc, h1⟩, h2⟩
        exact ⟨r, w, c, L₁' ++ L₂, rfl, he, hc, L₁', L₂, rfl, h1, h2⟩

/-! ## Cones -/

theorem mem_cone_iff (u : Seq) (ξ : Str) : ξ ∈ cone u ↔ ∃ η, u ++ₛ η = ξ := Iff.rfl

theorem append_mem_cone (u : Seq) (η : Str) : u ++ₛ η ∈ cone u := ⟨η, rfl⟩

theorem append_mem_cone_append_iff (s v : Seq) (ξ : Str) :
    s ++ₛ ξ ∈ cone (s ++ v) ↔ ξ ∈ cone v := by
  simp only [mem_cone_iff, Stream'.append_append_stream, Stream'.append_right_inj]

theorem cons_not_mem_cone_cons {a b : Bool} (h : a ≠ b) (l l' : Seq) (η : Str) :
    (a :: l) ++ₛ η ∉ cone (b :: l') := by
  rintro ⟨η', h'⟩
  have := congrArg Stream'.head h'
  simp [Stream'.cons_append_stream] at this
  exact h this.symm

theorem not_mem_cone_of_ne {a b : Bool} (h : a ≠ b) (s l l' : Seq) (η : Str) :
    (s ++ a :: l) ++ₛ η ∉ cone (s ++ b :: l') := by
  rw [Stream'.append_append_stream, append_mem_cone_append_iff]
  exact cons_not_mem_cone_cons h l l' η

/-! ## The start word -/

theorem act_W0_take3 :
    act (W0.take 3) = genP (.y [true]) ^ (-1 : ℤ) *
      (genP (.y [false, true]) ^ (-1 : ℤ) * (genP (.y [false, false]) ^ (-1 : ℤ) * 1)) := by
  simp [act, W0, mul_assoc]

theorem frozen_W0 : Frozen W0 := by
  refine ⟨[(.A, [], false), (.B, [], false), (.C, [], false), (.D, [], true)], Forest.init, ?_⟩
  simp only [W0, Good]
  refine ⟨by simp, fun η => rfl, by simp, fun η => ?_, by simp, fun η => ?_, by simp, fun η => ?_,
    trivial⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, psi]
    exact genP_y_zpow_of_not_mem _ _ _
      (not_mem_cone_of_ne (s := [false]) (a := true) (b := false) (by decide) [] [] η)
  · simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, psi, Stream'.nil_append_stream]
    rw [genP_y_zpow_of_not_mem [false, false] (-1) ([true] ++ₛ η)
      (not_mem_cone_of_ne (s := []) (a := true) (b := false) (by decide) [] [false] η)]
    exact genP_y_zpow_of_not_mem _ _ _
      (not_mem_cone_of_ne (s := []) (a := true) (b := false) (by decide) [] [true] η)
  · show (genP (.y [true]) ^ (-1 : ℤ) *
      (genP (.y [false, true]) ^ (-1 : ℤ) * (genP (.y [false, false]) ^ (-1 : ℤ) * 1)))
        ((act (W0.take 3)).symm η) = η
    rw [← act_W0_take3]
    exact Equiv.apply_symm_apply _ _

/-! ## Membership in cones of concrete shape -/

theorem mem_cone_nil (ξ : Str) : ξ ∈ cone [] := ⟨ξ, rfl⟩

theorem cons_append_mem_cone_cons_iff (a b : Bool) (l l' : Seq) (η : Str) :
    (a :: l) ++ₛ η ∈ cone (b :: l') ↔ a = b ∧ l ++ₛ η ∈ cone l' := by
  simp only [mem_cone_iff, Stream'.cons_append_stream]
  constructor
  · rintro ⟨η', h'⟩
    have h1 := congrArg Stream'.head h'
    have h2 := congrArg Stream'.tail h'
    simp only [Stream'.head_cons, Stream'.tail_cons] at h1 h2
    exact ⟨h1.symm, η', h2⟩
  · rintro ⟨rfl, η', h'⟩
    exact ⟨η', by rw [h']⟩

/-! ## The values of `x_s` and `x_s⁻¹` on the three subcones of `[s]` -/

theorem genP_x_apply (s : Seq) (ξ : Str) : genP (.x s) ξ = localize s xFun ξ := rfl

theorem gx_00 (s : Seq) (η : Str) :
    genP (.x s) (s ++ₛ ([false, false] ++ₛ η)) = s ++ₛ ([false] ++ₛ η) := by
  rw [genP_x_apply, localize_append, xFun_00]

theorem gx_01 (s : Seq) (η : Str) :
    genP (.x s) (s ++ₛ ([false, true] ++ₛ η)) = s ++ₛ ([true, false] ++ₛ η) := by
  rw [genP_x_apply, localize_append, xFun_01]

theorem gx_1 (s : Seq) (η : Str) :
    genP (.x s) (s ++ₛ ([true] ++ₛ η)) = s ++ₛ ([true, true] ++ₛ η) := by
  rw [genP_x_apply, localize_append, xFun_1]

theorem gxinv_0 (s : Seq) (η : Str) :
    (genP (.x s))⁻¹ (s ++ₛ ([false] ++ₛ η)) = s ++ₛ ([false, false] ++ₛ η) := by
  rw [Equiv.Perm.inv_eq_iff_eq, gx_00]

theorem gxinv_10 (s : Seq) (η : Str) :
    (genP (.x s))⁻¹ (s ++ₛ ([true, false] ++ₛ η)) = s ++ₛ ([false, true] ++ₛ η) := by
  rw [Equiv.Perm.inv_eq_iff_eq, gx_01]

theorem gxinv_11 (s : Seq) (η : Str) :
    (genP (.x s))⁻¹ (s ++ₛ ([true, true] ++ₛ η)) = s ++ₛ ([true] ++ₛ η) := by
  rw [Equiv.Perm.inv_eq_iff_eq, gx_1]

/-! ## Regions of consecutive labels -/

/-- The region of a label is the preimage of its subscript's cone under the prefix value. -/
theorem region_eq_preimage {f : Equiv.Perm Str} {l : Label} {t : Seq}
    (h : ∀ η, f (psi l.1 (l.2.1 ++ₛ η)) = t ++ₛ η) : region l = f ⁻¹' cone t := by
  ext x
  simp only [region, Set.mem_image, Set.mem_preimage, cone, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
    exact ⟨η, (h η).symm⟩
  · rintro ⟨η, hη⟩
    refine ⟨l.2.1 ++ₛ η, ⟨η, rfl⟩, f.injective ?_⟩
    rw [h, hη]

/-- Two consecutive letters with the same subscript `t` have equal regions. -/
theorem region_eq_of_same {f : Equiv.Perm Str} {l₁ l₂ : Label} {t : Seq} {i : ℤ}
    (h₁ : ∀ η, f (psi l₁.1 (l₁.2.1 ++ₛ η)) = t ++ₛ η)
    (h₂ : ∀ η, (genP (.y t) ^ i * f) (psi l₂.1 (l₂.2.1 ++ₛ η)) = t ++ₛ η) :
    region l₁ = region l₂ := by
  rw [region_eq_preimage h₁, region_eq_preimage h₂]
  ext x
  simp only [Set.mem_preimage, Equiv.Perm.mul_apply, genP_y_zpow_mem_iff]

/-- Facts about two consecutive labels of a forest. -/
theorem forest_pair {La Lc : List Label} {l₁ l₂ : Label} (hF : Forest (La ++ [l₁, l₂] ++ Lc)) :
    region l₁ ≠ region l₂ ∧ ¬ (l₁.2.2 = true ∧ l₂.2.2 = true) := by
  have hlen : La.length + 1 < (La ++ [l₁, l₂] ++ Lc).length := by simp
  have e1 : (La ++ [l₁, l₂] ++ Lc)[La.length] = l₁ := by
    simp [List.getElem_append_right]
  have e2 : (La ++ [l₁, l₂] ++ Lc)[La.length + 1] = l₂ := by
    simp [List.getElem_append_right]
  have h1 := hF.region_ne La.length hlen
  have h2 := hF.not_pos_pos La.length hlen
  simp only [e1, e2] at h1 h2
  exact ⟨h1, h2⟩

/-! ## Replacing a block -/

/-- If a block `B` can be replaced by `B'` of the same value, keeping `Good` and the forest, then
`pre ++ B' ++ post` is frozen whenever `pre ++ B ++ post` is. -/
theorem frozen_replace {pre B B' post : Word} (hV : Frozen (pre ++ B ++ post))
    (hact : act B = act B')
    (hB : ∀ f La Lb Lc, Forest (La ++ Lb ++ Lc) → Good f B Lb →
      ∃ Lb', Forest (La ++ Lb' ++ Lc) ∧ Good f B' Lb') :
    Frozen (pre ++ B' ++ post) := by
  obtain ⟨L, hF, hG⟩ := hV
  obtain ⟨L₁, Lc, rfl, h1, hpost⟩ := (LM56.PartG.good_append _ _ _ _).1 hG
  obtain ⟨La, Lb, rfl, hpre, hblk⟩ := (LM56.PartG.good_append _ _ _ _).1 h1
  obtain ⟨Lb', hF', hblk'⟩ := hB _ La Lb Lc hF hblk
  refine ⟨La ++ Lb' ++ Lc, hF', (LM56.PartG.good_append _ _ _ _).2
    ⟨La ++ Lb', Lc, rfl, (LM56.PartG.good_append _ _ _ _).2 ⟨La, Lb', rfl, hpre, hblk'⟩, ?_⟩⟩
  rwa [act_append, ← hact, ← act_append]

/-! ## The blocks -/

theorem block_moveX {s t t' : Seq} {i : ℤ} (h : xFin s t = some t') (f : Equiv.Perm Str)
    (Lb : List Label) (hG : Good f [(.y t, i), (.x s, 1)] Lb) :
    Good f [(.x s, 1), (.y t', i)] Lb := by
  simp only [good_y', good_x', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, rfl⟩ := hG
  simp only [Good]
  refine ⟨he, fun η => ?_, trivial⟩
  rw [Equiv.Perm.mul_apply, hc, zpow_one, genP_x_of_xFin h]

theorem block_moveXInv {s t t' : Seq} {i : ℤ} (h : xFinInv s t = some t') (f : Equiv.Perm Str)
    (Lb : List Label) (hG : Good f [(.y t, i), (.x s, -1)] Lb) :
    Good f [(.x s, -1), (.y t', i)] Lb := by
  simp only [good_y', good_x', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, rfl⟩ := hG
  simp only [Good]
  refine ⟨he, fun η => ?_, trivial⟩
  rw [Equiv.Perm.mul_apply, hc, zpow_neg_one, genP_x_inv_of_xFinInv h]

theorem block_expand (s : Seq) (f : Equiv.Perm Str) (La Lb Lc : List Label)
    (hF : Forest (La ++ Lb ++ Lc)) (hG : Good f [(.y s, 1)] Lb) :
    ∃ Lb', Forest (La ++ Lb' ++ Lc) ∧
      Good f [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
        (.y (s ++ [true, true]), 1)] Lb' := by
  simp only [good_y', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, rfl⟩ := hG
  cases c
  · simp at he
  refine ⟨[(r, w ++ [false, false], true), (r, w ++ [false, true], false), (r, w ++ [true], true)],
    Forest.expandPos La Lc r w hF, ?_⟩
  simp only [Good]
  refine ⟨rfl, fun η => ?_, rfl, fun η => ?_, rfl, fun η => ?_, trivial⟩
  · simp only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_one (genP (.x s)),
      gx_00]
  · simp (disch := simp only [append_mem_cone_append_iff, cons_append_mem_cone_cons_iff,
        Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, true_and, not_false_eq_true])
      only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_one (genP (.x s)),
      gx_01, genP_y_zpow_of_not_mem]
  · simp (disch := simp only [append_mem_cone_append_iff, cons_append_mem_cone_cons_iff,
        Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, true_and, not_false_eq_true])
      only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_one (genP (.x s)),
      gx_1, genP_y_zpow_of_not_mem]

theorem block_expandInv (s : Seq) (f : Equiv.Perm Str) (La Lb Lc : List Label)
    (hF : Forest (La ++ Lb ++ Lc)) (hG : Good f [(.y s, -1)] Lb) :
    ∃ Lb', Forest (La ++ Lb' ++ Lc) ∧
      Good f [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
        (.y (s ++ [true]), -1)] Lb' := by
  simp only [good_y', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, rfl⟩ := hG
  cases c
  swap
  · simp at he
  refine ⟨[(r, w ++ [false], false), (r, w ++ [true, false], true), (r, w ++ [true, true], false)],
    Forest.expandNeg La Lc r w hF, ?_⟩
  simp only [Good]
  refine ⟨rfl, fun η => ?_, rfl, fun η => ?_, rfl, fun η => ?_, trivial⟩
  · simp only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_neg_one (genP (.x s)),
      gxinv_0]
  · simp (disch := simp only [append_mem_cone_append_iff, cons_append_mem_cone_cons_iff,
        Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, true_and, not_false_eq_true])
      only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_neg_one (genP (.x s)),
      gxinv_10, genP_y_zpow_of_not_mem]
  · simp (disch := simp only [append_mem_cone_append_iff, cons_append_mem_cone_cons_iff,
        Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, true_and, not_false_eq_true])
      only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_neg_one (genP (.x s)),
      gxinv_11, genP_y_zpow_of_not_mem]

/-- A pair of `y`-letters in a frozen word: its two labels are consecutive labels of the forest. -/
theorem good_pair {f : Equiv.Perm Str} {u v : Seq} {i j : ℤ} {Lb : List Label}
    (hG : Good f [(.y u, i), (.y v, j)] Lb) :
    ∃ l₁ l₂, Lb = [l₁, l₂] ∧ i = (if l₁.2.2 then 1 else -1) ∧ j = (if l₂.2.2 then 1 else -1) ∧
      (∀ η, f (psi l₁.1 (l₁.2.1 ++ₛ η)) = u ++ₛ η) ∧
      (∀ η, (genP (.y u) ^ i * f) (psi l₂.1 (l₂.2.1 ++ₛ η)) = v ++ₛ η) := by
  simp only [good_y', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, r', w', c', L'', rfl, he', hc', rfl⟩ := hG
  exact ⟨(r, w, c), (r', w', c'), rfl, he, he', hc, hc'⟩

theorem block_commute {u v : Seq} {i j : ℤ} (hi : 0 < i) (hj : 0 < j) (f : Equiv.Perm Str)
    (La Lb Lc : List Label) (hF : Forest (La ++ Lb ++ Lc)) (hG : Good f [(.y u, i), (.y v, j)] Lb) :
    False := by
  obtain ⟨l₁, l₂, rfl, he, he', -, -⟩ := good_pair hG
  refine (forest_pair hF).2 ⟨?_, ?_⟩
  · cases h : l₁.2.2
    · rw [h] at he; simp at he; omega
    · rfl
  · cases h : l₂.2.2
    · rw [h] at he'; simp at he'; omega
    · rfl

theorem block_same {t : Seq} {i j : ℤ} (f : Equiv.Perm Str)
    (La Lb Lc : List Label) (hF : Forest (La ++ Lb ++ Lc)) (hG : Good f [(.y t, i), (.y t, j)] Lb) :
    False := by
  obtain ⟨l₁, l₂, rfl, -, -, hc, hc'⟩ := good_pair hG
  exact (forest_pair hF).1 (region_eq_of_same hc hc')

theorem block_split_y {t : Seq} {i j : ℤ} (hij : 0 < i * j)
    (f : Equiv.Perm Str) (Lb : List Label) (hG : Good f [(.y t, i + j)] Lb) : False := by
  simp only [good_y', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, -, rfl⟩ := hG
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    cases c <;> simp at he <;> omega

theorem block_x_one {s : Seq} {n : ℤ} (f : Equiv.Perm Str) (Lb : List Label)
    (hG : Good f [(.x s, n)] Lb) : Lb = [] := by
  simpa only [good_x', good_nil'] using hG

theorem block_x_two (s : Seq) (i j : ℤ) (f : Equiv.Perm Str) : Good f [(.x s, i), (.x s, j)] [] := by
  simp [Good]

theorem block_x_one' (s : Seq) (n : ℤ) (f : Equiv.Perm Str) : Good f [(.x s, n)] [] := by
  simp [Good]

theorem block_x_two' {s : Seq} {i j : ℤ} (f : Equiv.Perm Str) (Lb : List Label)
    (hG : Good f [(.x s, i), (.x s, j)] Lb) : Lb = [] := by
  simpa only [good_x', good_nil'] using hG

/-! ## The invariant is preserved -/

/-- `act_posStep` on a block alone. -/
theorem act_block {B B' : Word} (h : PosStep ([] ++ B ++ []) ([] ++ B' ++ [])) : act B = act B' := by
  simpa only [List.nil_append, List.append_nil] using act_posStep h

theorem frozen_posStep {V V' : Word} (hV : Frozen V) (h : PosStep V V') : Frozen V' := by
  cases h with
  | moveX pre post s t t' i h =>
    exact frozen_replace hV (act_block (.moveX [] [] s t t' i h))
      fun f La Lb Lc hF hG => ⟨Lb, hF, block_moveX h f Lb hG⟩
  | moveXInv pre post s t t' i h =>
    exact frozen_replace hV (act_block (.moveXInv [] [] s t t' i h))
      fun f La Lb Lc hF hG => ⟨Lb, hF, block_moveXInv h f Lb hG⟩
  | expand pre post s =>
    exact frozen_replace hV (act_block (.expand [] [] s))
      fun f La Lb Lc hF hG => block_expand s f La Lb Lc hF hG
  | expandInv pre post s =>
    exact frozen_replace hV (act_block (.expandInv [] [] s))
      fun f La Lb Lc hF hG => block_expandInv s f La Lb Lc hF hG
  | commute pre post u v i j hi hj h =>
    exact frozen_replace hV (act_block (.commute [] [] u v i j hi hj h))
      fun f La Lb Lc hF hG => (block_commute hi hj f La Lb Lc hF hG).elim
  | split pre post g i j hi hj hij =>
    refine frozen_replace hV (act_block (.split [] [] g i j hi hj hij)) ?_
    intro f La Lb Lc hF hG
    cases g with
    | x s =>
      obtain rfl := block_x_one f Lb hG
      exact ⟨[], hF, block_x_two s i j f⟩
    | y t => exact (block_split_y hij f Lb hG).elim
  | merge pre post g i j hi hj hij =>
    refine frozen_replace hV (act_block (.merge [] [] g i j hi hj hij)) ?_
    intro f La Lb Lc hF hG
    cases g with
    | x s =>
      obtain rfl := block_x_two' f Lb hG
      exact ⟨[], hF, block_x_one' s (i + j) f⟩
    | y t => exact (block_same f La Lb Lc hF hG).elim
  | cancel pre post s i hi =>
    have := frozen_replace (B' := []) hV (act_block (.cancel [] [] s i hi))
      fun f La Lb Lc hF hG => (block_same f La Lb Lc hF hG).elim
    simpa only [List.append_nil] using this

end LM56.PartG
