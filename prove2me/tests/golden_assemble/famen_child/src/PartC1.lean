import Solutions.FAmenChild.Blueprint
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_bijOn_dyadic

/-!
# Part C1: one-sided slope exponents and the slope-jump cocycle of `F`

`rexp_spec`, `lexp_spec`, `jumpFun_finite`, `cocycle_support`, `cocycle_mul` of
`Solutions/FAmenChild/Blueprint.lean`.
-/

open scoped ENNReal Pointwise
open CannonFloydParry

namespace FAmenChild.PartC1

open FAmenChild

/-! ### Elementary helpers -/

/-- Two affine maps with power-of-two slopes that agree at two distinct points have the same
slope exponent. -/
lemma zpow_eq_of_two_points {n m : ℤ} {c c' p q : ℝ} (hpq : p < q)
    (hp : (2 : ℝ) ^ n * p + c = 2 ^ m * p + c') (hq : (2 : ℝ) ^ n * q + c = 2 ^ m * q + c') :
    n = m := by
  have h : (2 : ℝ) ^ n * (q - p) = 2 ^ m * (q - p) := by linarith
  have h2 : (2 : ℝ) ^ n = 2 ^ m := mul_right_cancel₀ (sub_ne_zero.mpr hpq.ne') h
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h2

/-- A finite set of reals stays a positive distance (below any prescribed `ε`) from any point
other than its own elements. -/
lemma exists_gap (B : Finset ℝ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ ≤ ε ∧ ∀ b ∈ B, b ≠ x → δ ≤ |b - x| := by
  induction B using Finset.induction_on with
  | empty => exact ⟨ε, hε, le_rfl, by simp⟩
  | insert b B _ ih =>
    obtain ⟨δ, hδ, hδε, hδB⟩ := ih
    by_cases hbx : b = x
    · refine ⟨δ, hδ, hδε, ?_⟩
      intro t ht htx
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact absurd hbx htx
      · exact hδB t ht htx
    · refine ⟨min δ |b - x|, lt_min hδ (abs_pos.mpr (sub_ne_zero.mpr hbx)),
        (min_le_left _ _).trans hδε, ?_⟩
      intro t ht htx
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hδB t ht htx)

lemma inter_eq_empty_of_gap {B : Finset ℝ} {x δ a b : ℝ}
    (hδB : ∀ t ∈ B, t ≠ x → δ ≤ |t - x|) (hxB : ∀ t ∈ B, t ∈ Set.Ioo a b → t ≠ x)
    (hab : ∀ t ∈ Set.Ioo a b, |t - x| < δ) : Set.Ioo a b ∩ (B : Set ℝ) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ⟨ht, htB⟩ => ?_
  have := hδB t htB (hxB t htB ht)
  have := hab t ht
  linarith

/-- The image of a point of `D` under an element of `F` is in `D`. -/
lemma mapsTo_D {g : UI ≃o UI} (hg : g ∈ F) {x : UI} (hx : x ∈ D) : g x ∈ D := by
  obtain ⟨h0, h1, hd⟩ := hx
  refine ⟨?_, ?_, (bijOn_dyadic hg).mapsTo hd⟩
  · have hlt : (⟨0, zero_mem_UI⟩ : UI) < x := h0
    have h2 : g ⟨0, zero_mem_UI⟩ < g x := g.lt_iff_lt.mpr hlt
    exact lt_of_le_of_lt (g ⟨0, zero_mem_UI⟩).2.1 h2
  · have hlt : x < (⟨1, one_mem_UI⟩ : UI) := h1
    have h2 : g x < g ⟨1, one_mem_UI⟩ := g.lt_iff_lt.mpr hlt
    exact lt_of_lt_of_le h2 (g ⟨1, one_mem_UI⟩).2.2

lemma lt_one_apply {g : UI ≃o UI} {x : UI} (hx : (x : ℝ) < 1) : (g x : ℝ) < 1 := by
  have hlt : x < (⟨1, one_mem_UI⟩ : UI) := hx
  have h2 : g x < g ⟨1, one_mem_UI⟩ := g.lt_iff_lt.mpr hlt
  exact lt_of_lt_of_le h2 (g ⟨1, one_mem_UI⟩).2.2

lemma pos_apply {g : UI ≃o UI} {x : UI} (hx : 0 < (x : ℝ)) : 0 < (g x : ℝ) := by
  have hlt : (⟨0, zero_mem_UI⟩ : UI) < x := hx
  have h2 : g ⟨0, zero_mem_UI⟩ < g x := g.lt_iff_lt.mpr hlt
  exact lt_of_le_of_lt (g ⟨0, zero_mem_UI⟩).2.1 h2

/-! ### The one-sided slope exponents -/

/-- Any power-of-two slope that `f` has just to the right of `x` is `2 ^ rexp f x`. -/
lemma rexp_eq {f : UI ≃o UI} {x : UI} (hx : (x : ℝ) < 1) {n : ℤ} {c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ → (f z : ℝ) = 2 ^ n * z + c) :
    rexp f x = n := by
  have hex : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ n * z + c := ⟨n, c, δ, hδ, h⟩
  unfold rexp
  rw [dif_pos hex]
  obtain ⟨c', δ', hδ', h'⟩ := hex.choose_spec
  set ε := min (min δ δ') (1 - x) with hε
  have hε0 : 0 < ε := lt_min (lt_min hδ hδ') (sub_pos.mpr hx)
  have hε1 : ε ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ δ' := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ 1 - x := min_le_right _ _
  have hy : (x : ℝ) + ε ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [x.2.1], by linarith⟩
  have hx1 : (x : ℝ) ≤ x + δ := by linarith
  have hx2 : (x : ℝ) ≤ x + δ' := by linarith
  refine zpow_eq_of_two_points (p := x) (q := x + ε) (c := c') (c' := c) (by linarith)
    ((h' x le_rfl hx2).symm.trans (h x le_rfl hx1))
    ((h' ⟨_, hy⟩ (by simp; linarith) (by simp; linarith)).symm.trans
      (h ⟨_, hy⟩ (by simp; linarith) (by simp; linarith)))

/-- Any power-of-two slope that `f` has just to the left of `x` is `2 ^ lexp f x`. -/
lemma lexp_eq {f : UI ≃o UI} {x : UI} (hx : 0 < (x : ℝ)) {n : ℤ} {c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x → (f z : ℝ) = 2 ^ n * z + c) :
    lexp f x = n := by
  have hex : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ n * z + c := ⟨n, c, δ, hδ, h⟩
  unfold lexp
  rw [dif_pos hex]
  obtain ⟨c', δ', hδ', h'⟩ := hex.choose_spec
  set ε := min (min δ δ') (x : ℝ) with hε
  have hε0 : 0 < ε := lt_min (lt_min hδ hδ') hx
  have hε1 : ε ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ δ' := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ x := min_le_right _ _
  have hy : (x : ℝ) - ε ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [x.2.2]⟩
  have hx1 : (x : ℝ) - δ ≤ x := by linarith
  have hx2 : (x : ℝ) - δ' ≤ x := by linarith
  refine zpow_eq_of_two_points (p := x - ε) (q := x) (c := c') (c' := c) (by linarith)
    ((h' ⟨_, hy⟩ (by simp; linarith) (by simp; linarith)).symm.trans
      (h ⟨_, hy⟩ (by simp; linarith) (by simp; linarith)))
    ((h' x hx2 le_rfl).symm.trans (h x hx1 le_rfl))

theorem rexp_spec {f : UI ≃o UI} (hf : f ∈ F) {x : UI} (hx : (x : ℝ) < 1) :
    ∃ c δ : ℝ, 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ rexp f x * z + c := by
  have hex : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ n * z + c := by
    obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp hf
    obtain ⟨δ, hδ, hδε, hδB⟩ := exists_gap B (x : ℝ) (sub_pos.mpr hx)
    have hy : (x : ℝ) + δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [x.2.1], by linarith⟩
    obtain ⟨n, c, hnc⟩ := hB x ⟨_, hy⟩ (by simp; linarith)
      (inter_eq_empty_of_gap hδB (fun t _ ht => ne_of_gt ht.1)
        (fun t ht => by rw [abs_of_pos (by linarith [ht.1])]; simp at ht; linarith [ht.2]))
    exact ⟨n, c, δ, hδ, fun z h1 h2 => hnc z ⟨h1, h2⟩⟩
  unfold rexp
  rw [dif_pos hex]
  exact hex.choose_spec

theorem lexp_spec {f : UI ≃o UI} (hf : f ∈ F) {x : UI} (hx : 0 < (x : ℝ)) :
    ∃ c δ : ℝ, 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ lexp f x * z + c := by
  have hex : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ n * z + c := by
    obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp hf
    obtain ⟨δ, hδ, hδε, hδB⟩ := exists_gap B (x : ℝ) hx
    have hy : (x : ℝ) - δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [x.2.2]⟩
    obtain ⟨n, c, hnc⟩ := hB ⟨_, hy⟩ x (by simp; linarith)
      (inter_eq_empty_of_gap hδB (fun t _ ht => ne_of_lt (by simpa using ht.2))
        (fun t ht => by
          simp at ht
          rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1]))
    exact ⟨n, c, δ, hδ, fun z h1 h2 => hnc z ⟨h1, h2⟩⟩
  unfold lexp
  rw [dif_pos hex]
  exact hex.choose_spec

theorem jumpFun_finite {f : UI ≃o UI} (hf : f ∈ F) : (Function.support (jumpFun f)).Finite := by
  obtain ⟨B, -, hB⟩ := mem_F_iff_isThompson.mp hf
  refine (B.finite_toSet.preimage Subtype.val_injective.injOn).subset ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxB
  have hxB' : (x : ℝ) ∉ B := by simpa using hxB
  apply hx
  unfold jumpFun
  split_ifs with hD
  · obtain ⟨h0, h1, -⟩ := hD
    obtain ⟨δ, hδ, hδε, hδB⟩ := exists_gap B (x : ℝ) (lt_min h0 (sub_pos.mpr h1))
    have hδ0 : δ ≤ x := hδε.trans (min_le_left _ _)
    have hδ1 : δ ≤ 1 - x := hδε.trans (min_le_right _ _)
    have ha : (x : ℝ) - δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [x.2.2]⟩
    have hb : (x : ℝ) + δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [x.2.1], by linarith⟩
    obtain ⟨n, c, hnc⟩ := hB ⟨_, ha⟩ ⟨_, hb⟩ (by simp; linarith)
      (inter_eq_empty_of_gap hδB (fun t htB _ htx => hxB' (htx ▸ htB))
        (fun t ht => by simp at ht; rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]))
    rw [rexp_eq h1 hδ (fun z hz1 hz2 => hnc z ⟨by simp; linarith, hz2⟩),
      lexp_eq h0 hδ (fun z hz1 hz2 => hnc z ⟨hz1, by simp; linarith⟩), sub_self]
  · rfl

/-! ### The cocycle -/

theorem cocycle_support (g : F) : (↑(cocycle g).support : Set UI) ⊆ D := by
  classical
  intro y hy
  have hy' := Finsupp.mapDomain_support (f := fun x => g • x) (s := jump g) hy
  rw [Finset.mem_image] at hy'
  obtain ⟨x, hx, rfl⟩ := hy'
  have hxD : x ∈ D := by
    by_contra hD
    rw [Finsupp.mem_support_iff] at hx
    apply hx
    simp only [jump, Finsupp.ofSupportFinite_coe, jumpFun]
    rw [if_neg hD]
  exact mapsTo_D g.2 hxD

/-- The chain rule for right slope exponents. -/
lemma rexp_mul {g h : UI ≃o UI} (hg : g ∈ F) (hh : h ∈ F) {x : UI} (hx : (x : ℝ) < 1) :
    rexp (g * h) x = rexp g (h x) + rexp h x := by
  obtain ⟨c1, δ1, hδ1, h1⟩ := rexp_spec hh hx
  obtain ⟨c2, δ2, hδ2, h2⟩ := rexp_spec hg (lt_one_apply (g := h) hx)
  have ha : (0 : ℝ) < 2 ^ rexp h x := zpow_pos two_pos _
  refine rexp_eq hx (c := 2 ^ rexp g (h x) * c1 + c2) (δ := min δ1 (δ2 / 2 ^ rexp h x))
    (lt_min hδ1 (div_pos hδ2 ha)) ?_
  intro z hz1 hz2
  have hzd1 : (z : ℝ) ≤ x + δ1 := hz2.trans (by linarith [min_le_left δ1 (δ2 / 2 ^ rexp h x)])
  have hzd2 : (z : ℝ) - x ≤ δ2 / 2 ^ rexp h x := by
    linarith [min_le_right δ1 (δ2 / 2 ^ rexp h x)]
  have e1 := h1 z hz1 hzd1
  have e0 := h1 x le_rfl (by linarith)
  have hdiff : (h z : ℝ) - h x = 2 ^ rexp h x * ((z : ℝ) - x) := by rw [e1, e0]; ring
  have hle1 : (h x : ℝ) ≤ h z := by
    have := mul_nonneg ha.le (sub_nonneg.mpr hz1); linarith
  have hle2 : (h z : ℝ) ≤ h x + δ2 := by
    have := mul_le_mul_of_nonneg_left hzd2 ha.le
    rw [mul_div_cancel₀ _ ha.ne'] at this; linarith
  rw [RelIso.mul_apply, h2 (h z) hle1 hle2, e1, zpow_add₀ two_ne_zero]
  ring

/-- The chain rule for left slope exponents. -/
lemma lexp_mul {g h : UI ≃o UI} (hg : g ∈ F) (hh : h ∈ F) {x : UI} (hx : 0 < (x : ℝ)) :
    lexp (g * h) x = lexp g (h x) + lexp h x := by
  obtain ⟨c1, δ1, hδ1, h1⟩ := lexp_spec hh hx
  obtain ⟨c2, δ2, hδ2, h2⟩ := lexp_spec hg (pos_apply (g := h) hx)
  have ha : (0 : ℝ) < 2 ^ lexp h x := zpow_pos two_pos _
  refine lexp_eq hx (c := 2 ^ lexp g (h x) * c1 + c2) (δ := min δ1 (δ2 / 2 ^ lexp h x))
    (lt_min hδ1 (div_pos hδ2 ha)) ?_
  intro z hz1 hz2
  have hzd1 : (x : ℝ) - δ1 ≤ z := le_trans (by linarith [min_le_left δ1 (δ2 / 2 ^ lexp h x)]) hz1
  have hzd2 : (x : ℝ) - z ≤ δ2 / 2 ^ lexp h x := by
    linarith [min_le_right δ1 (δ2 / 2 ^ lexp h x)]
  have e1 := h1 z hzd1 hz2
  have e0 := h1 x (by linarith) le_rfl
  have hdiff : (h x : ℝ) - h z = 2 ^ lexp h x * ((x : ℝ) - z) := by rw [e1, e0]; ring
  have hle1 : (h z : ℝ) ≤ h x := by
    have := mul_nonneg ha.le (sub_nonneg.mpr hz2); linarith
  have hle2 : (h x : ℝ) - δ2 ≤ h z := by
    have := mul_le_mul_of_nonneg_left hzd2 ha.le
    rw [mul_div_cancel₀ _ ha.ne'] at this; linarith
  rw [RelIso.mul_apply, h2 (h z) hle2 hle1, e1, zpow_add₀ two_ne_zero]
  ring

lemma jumpFun_mul {g h : UI ≃o UI} (hg : g ∈ F) (hh : h ∈ F) (x : UI) :
    jumpFun (g * h) x = jumpFun g (h x) + jumpFun h x := by
  by_cases hD : x ∈ D
  · have hhD : h x ∈ D := mapsTo_D hh hD
    unfold jumpFun
    rw [if_pos hD, if_pos hD, if_pos hhD, rexp_mul hg hh hD.2.1, lexp_mul hg hh hD.1]
    ring
  · have hhD : h x ∉ D := fun h' => hD (by simpa using mapsTo_D (inv_mem hh) h')
    unfold jumpFun
    rw [if_neg hD, if_neg hD, if_neg hhD, add_zero]

lemma jump_mul (g h : F) :
    jump (g * h) = Finsupp.mapDomain (fun x => h⁻¹ • x) (jump g) + jump h := by
  ext x
  have e : (Finsupp.mapDomain (fun x => h⁻¹ • x) (jump g)) x = jump g (h • x) := by
    conv_lhs => rw [← inv_smul_smul h x]
    exact Finsupp.mapDomain_apply (MulAction.injective h⁻¹) _ _
  rw [Finsupp.add_apply, e]
  simp only [jump, Finsupp.ofSupportFinite_coe]
  exact jumpFun_mul g.2 h.2 x

theorem cocycle_mul (g h : F) :
    cocycle (g * h) = cocycle g + Finsupp.mapDomain (fun x => g • x) (cocycle h) := by
  have e1 : (fun x : UI => (g * h) • x) ∘ (fun x => h⁻¹ • x) = fun x => g • x := by
    funext x; simp [mul_smul]
  have e2 : (fun x : UI => (g * h) • x) = (fun x => g • x) ∘ (fun x => h • x) := by
    funext x; simp [mul_smul]
  unfold cocycle
  rw [jump_mul, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, e1, e2,
    Finsupp.mapDomain_comp]

end FAmenChild.PartC1
