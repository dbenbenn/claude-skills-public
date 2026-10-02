import Solutions.FAmenChild.Blueprint
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson

/-!
# Part C2: the affine action `g ⋆ φ = cocycle g + g · φ` is free

Route (shorter than the weighted-length argument of the brief, same ingredients):

* From `cocycle g + g · φ = φ`, evaluating at `g x`: `jumpFun g x = φ (g x) - φ x`.
* For any Thompson map `f` and `p < q`, the jumps of `f` strictly between `p` and `q` add up to
  `lexp f q - rexp f p` (induction on the number of breakpoints of `f` in `(p, q)`).
* If `g` fixes `p` and `q`, it permutes `(p, q)`, so the cocycle relation makes that sum `0`:
  the slope exponent just right of `p` equals the one just left of `q`.
* If `g ≠ 1`, take a maximal interval `(p, q)` of moved points (`g - id` has constant sign
  there).  Near `p`, `g z - z = (2^n - 1)(z - p)`; near `q`, `g z - z = (2^n - 1)(z - q)` with
  the same `n`: these have opposite signs, a contradiction.
-/

open scoped ENNReal Pointwise
open CannonFloydParry

namespace FAmenChild.PartC2

open FAmenChild

/-! ### Uniqueness of slope exponents -/

theorem two_zpow_inj {n m : ℤ} (h : (2:ℝ) ^ n = 2 ^ m) : n = m :=
  zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h

/-- If `f` is affine with slope `2^n` on `[x, y]`, `x < y`, then `rexp f x = n`. -/
theorem rexp_eq_of_affine {f : UI ≃o UI} (hf : f ∈ F) {x y : UI} (hxy : (x:ℝ) < y) {n : ℤ}
    {c : ℝ} (h : ∀ z : UI, (x:ℝ) ≤ z → (z:ℝ) ≤ y → (f z : ℝ) = 2 ^ n * z + c) :
    rexp f x = n := by
  have hx1 : (x:ℝ) < 1 := lt_of_lt_of_le hxy y.2.2
  obtain ⟨c', δ, hδ, h'⟩ := rexp_spec hf hx1
  set t : ℝ := min ((x:ℝ) + δ) y with ht
  have htx : (x:ℝ) < t := lt_min (by linarith) hxy
  have hty : t ≤ y := min_le_right _ _
  have htd : t ≤ (x:ℝ) + δ := min_le_left _ _
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [x.2.1], le_trans hty y.2.2⟩
  have e1 : (f x : ℝ) = 2 ^ n * x + c := h x le_rfl hxy.le
  have e2 : (f x : ℝ) = 2 ^ rexp f x * x + c' := h' x le_rfl (by linarith)
  have e3 : (f ⟨t, htI⟩ : ℝ) = 2 ^ n * t + c := h ⟨t, htI⟩ htx.le hty
  have e4 : (f ⟨t, htI⟩ : ℝ) = 2 ^ rexp f x * t + c' := h' ⟨t, htI⟩ htx.le htd
  have key : (2:ℝ) ^ n * (t - x) = 2 ^ rexp f x * (t - x) := by
    linear_combination e1 - e3 + e4 - e2
  have hne : t - (x:ℝ) ≠ 0 := by linarith
  exact (two_zpow_inj (mul_right_cancel₀ hne key)).symm

/-- If `f` is affine with slope `2^n` on `[x, y]`, `x < y`, then `lexp f y = n`. -/
theorem lexp_eq_of_affine {f : UI ≃o UI} (hf : f ∈ F) {x y : UI} (hxy : (x:ℝ) < y) {n : ℤ}
    {c : ℝ} (h : ∀ z : UI, (x:ℝ) ≤ z → (z:ℝ) ≤ y → (f z : ℝ) = 2 ^ n * z + c) :
    lexp f y = n := by
  have hy0 : 0 < (y:ℝ) := lt_of_le_of_lt x.2.1 hxy
  obtain ⟨c', δ, hδ, h'⟩ := lexp_spec hf hy0
  set t : ℝ := max ((y:ℝ) - δ) x with ht
  have hty : t < (y:ℝ) := max_lt (by linarith) hxy
  have htx : (x:ℝ) ≤ t := le_max_right _ _
  have htd : (y:ℝ) - δ ≤ t := le_max_left _ _
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans x.2.1 htx, by linarith [y.2.2]⟩
  have e1 : (f y : ℝ) = 2 ^ n * y + c := h y hxy.le le_rfl
  have e2 : (f y : ℝ) = 2 ^ lexp f y * y + c' := h' y (by linarith) le_rfl
  have e3 : (f ⟨t, htI⟩ : ℝ) = 2 ^ n * t + c := h ⟨t, htI⟩ htx hty.le
  have e4 : (f ⟨t, htI⟩ : ℝ) = 2 ^ lexp f y * t + c' := h' ⟨t, htI⟩ htd hty.le
  have key : (2:ℝ) ^ n * (y - t) = 2 ^ lexp f y * (y - t) := by
    linear_combination e3 - e1 + e2 - e4
  have hne : (y:ℝ) - t ≠ 0 := by linarith
  exact (two_zpow_inj (mul_right_cancel₀ hne key)).symm

/-- No jump strictly inside an interval on which `f` is affine. -/
theorem jumpFun_eq_zero_of_affine {f : UI ≃o UI} (hf : f ∈ F) {p q : UI} {n : ℤ} {c : ℝ}
    (h : ∀ z : UI, (p:ℝ) ≤ z → (z:ℝ) ≤ q → (f z : ℝ) = 2 ^ n * z + c) {y : UI}
    (hpy : (p:ℝ) < y) (hyq : (y:ℝ) < q) : jumpFun f y = 0 := by
  have h1 : rexp f y = n :=
    rexp_eq_of_affine hf hyq (fun z hz1 hz2 => h z (by linarith) hz2)
  have h2 : lexp f y = n :=
    lexp_eq_of_affine hf hpy (fun z hz1 hz2 => h z hz1 (by linarith))
  unfold jumpFun
  split_ifs <;> simp [h1, h2]

/-! ### Telescoping the jumps -/

/-- The sum of the slope jumps of `f` strictly between `p` and `q`. -/
noncomputable def jsum (f : UI ≃o UI) (p q : UI) : ℤ := ∑ᶠ y ∈ Set.Ioo p q, jumpFun f y

theorem jsum_split {f : UI ≃o UI} (hf : f ∈ F) {p b q : UI} (hpb : p < b) (hbq : b < q) :
    jsum f p q = jumpFun f b + jsum f p b + jsum f b q := by
  have hfin : ∀ s : Set UI, (s ∩ Function.support (jumpFun f)).Finite :=
    fun s => (jumpFun_finite hf).subset Set.inter_subset_right
  unfold jsum
  rw [← Set.Ioc_union_Ioo_eq_Ioo hpb.le hbq, ← Set.Ioo_insert_right hpb]
  rw [finsum_mem_union' _ (hfin _) (hfin _)]
  · rw [finsum_mem_insert' _ (fun h => lt_irrefl _ h.2) (hfin _)]
  · rw [Set.Ioo_insert_right hpb]
    exact Set.disjoint_left.2 (fun y h1 h2 => absurd h2.1 (not_lt.2 h1.2))

/-- The jumps of a Thompson map over `(p, q)` add up to `lexp f q - rexp f p`. -/
theorem jsum_eq {f : UI ≃o UI} (hf : f ∈ F) {p q : UI} (hpq : p < q) :
    jsum f p q = lexp f q - rexp f p := by
  obtain ⟨B, hBd, hB⟩ := mem_F_iff_isThompson.1 hf
  suffices H : ∀ k : ℕ, ∀ p q : UI, p < q →
      (B.filter (fun b => (p:ℝ) < b ∧ b < q)).card ≤ k → jsum f p q = lexp f q - rexp f p from
    H _ p q hpq le_rfl
  intro k
  induction k with
  | zero =>
    intro p q hpq hk
    have hempty : Set.Ioo (p:ℝ) q ∩ (B : Set ℝ) = ∅ := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro ⟨h1, h2⟩ hb
      have : b ∈ B.filter (fun b => (p:ℝ) < b ∧ b < q) := Finset.mem_filter.2 ⟨hb, h1, h2⟩
      rw [Nat.le_zero, Finset.card_eq_zero] at hk
      simp [hk] at this
    obtain ⟨n, c, haff⟩ := hB p q hpq hempty
    have haff' : ∀ z : UI, (p:ℝ) ≤ z → (z:ℝ) ≤ q → (f z : ℝ) = 2 ^ n * z + c :=
      fun z h1 h2 => haff z ⟨h1, h2⟩
    rw [rexp_eq_of_affine hf hpq haff', lexp_eq_of_affine hf hpq haff', sub_self]
    exact finsum_mem_eq_zero_of_forall_eq_zero
      (fun y hy => jumpFun_eq_zero_of_affine hf haff' hy.1 hy.2)
  | succ k ih =>
    intro p q hpq hk
    by_cases hex : ∃ b ∈ B, (p:ℝ) < b ∧ b < q
    · obtain ⟨b, hbB, hpb, hbq⟩ := hex
      have hbI : b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [p.2.1], by linarith [q.2.2]⟩
      set bU : UI := ⟨b, hbI⟩ with hbU
      have hpb' : p < bU := hpb
      have hbq' : bU < q := hbq
      have hmem : b ∈ B.filter (fun b => (p:ℝ) < b ∧ b < q) := Finset.mem_filter.2 ⟨hbB, hpb, hbq⟩
      have hcard1 : (B.filter (fun x => (p:ℝ) < x ∧ x < (bU:ℝ))).card ≤ k := by
        have : (B.filter (fun x => (p:ℝ) < x ∧ x < (bU:ℝ))) ⊂
            B.filter (fun b => (p:ℝ) < b ∧ b < q) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨b, hmem, ?_⟩
            simp [bU]
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, hx.2.1, lt_trans hx.2.2 hbq⟩
        have := Finset.card_lt_card this
        omega
      have hcard2 : (B.filter (fun x => (bU:ℝ) < x ∧ x < q)).card ≤ k := by
        have : (B.filter (fun x => (bU:ℝ) < x ∧ x < q)) ⊂
            B.filter (fun b => (p:ℝ) < b ∧ b < q) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨b, hmem, ?_⟩
            simp [bU]
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, lt_trans hpb hx.2.1, hx.2.2⟩
        have := Finset.card_lt_card this
        omega
      have hD : bU ∈ D := ⟨by simpa [bU] using lt_of_le_of_lt p.2.1 hpb,
        by simpa [bU] using lt_of_lt_of_le hbq q.2.2, hBd b hbB⟩
      have hj : jumpFun f bU = rexp f bU - lexp f bU := by
        unfold jumpFun; rw [if_pos hD]
      rw [jsum_split hf hpb' hbq', hj, ih p bU hpb' hcard1, ih bU q hbq' hcard2]
      ring
    · have hempty : Set.Ioo (p:ℝ) q ∩ (B : Set ℝ) = ∅ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false,
          iff_false, not_and]
        rintro ⟨h1, h2⟩ hb
        exact hex ⟨b, hb, h1, h2⟩
      obtain ⟨n, c, haff⟩ := hB p q hpq hempty
      have haff' : ∀ z : UI, (p:ℝ) ≤ z → (z:ℝ) ≤ q → (f z : ℝ) = 2 ^ n * z + c :=
        fun z h1 h2 => haff z ⟨h1, h2⟩
      rw [rexp_eq_of_affine hf hpq haff', lexp_eq_of_affine hf hpq haff', sub_self]
      exact finsum_mem_eq_zero_of_forall_eq_zero
        (fun y hy => jumpFun_eq_zero_of_affine hf haff' hy.1 hy.2)

/-! ### The cocycle relation forces the jumps over a fixed interval to cancel -/

theorem jumpFun_eq_of_cocycle (g : F) (φ : UI →₀ ℤ)
    (h : cocycle g + Finsupp.mapDomain (fun x => g • x) φ = φ) (x : UI) :
    jumpFun (g : UI ≃o UI) x = φ ((g : UI ≃o UI) x) - φ x := by
  have e1 : (cocycle g) (g • x) = jump g x :=
    Finsupp.mapDomain_apply (MulAction.injective g) (jump g) x
  have e2 : (Finsupp.mapDomain (fun x => g • x) φ) (g • x) = φ x :=
    Finsupp.mapDomain_apply (MulAction.injective g) φ x
  have e3 : jump g x = jumpFun (g : UI ≃o UI) x := by
    rw [jump, Finsupp.ofSupportFinite_coe]
  have := DFunLike.congr_fun h (g • x)
  rw [Finsupp.add_apply, e1, e2, e3] at this
  change jumpFun (g : UI ≃o UI) x + φ x = φ ((g : UI ≃o UI) x) at this
  omega

theorem jsum_eq_zero_of_cocycle (g : F) (φ : UI →₀ ℤ)
    (h : cocycle g + Finsupp.mapDomain (fun x => g • x) φ = φ) {p q : UI}
    (hp : (g : UI ≃o UI) p = p) (hq : (g : UI ≃o UI) q = q) :
    jsum (g : UI ≃o UI) p q = 0 := by
  set f : UI ≃o UI := (g : UI ≃o UI) with hfdef
  have hf : f ∈ F := g.2
  have hrel := jumpFun_eq_of_cocycle g φ h
  have hfinφ : ∀ s : Set UI, (s ∩ Function.support φ).Finite :=
    fun s => φ.support.finite_toSet.subset (by rw [← Finsupp.fun_support_eq]; exact Set.inter_subset_right)
  have hfinJ : ∀ s : Set UI, (s ∩ Function.support (jumpFun f)).Finite :=
    fun s => (jumpFun_finite hf).subset Set.inter_subset_right
  -- `∑ φ ∘ f = ∑ φ` over `(p, q)`, since `f` permutes `(p, q)`.
  have hbij : Set.BijOn f (Set.Ioo p q) (Set.Ioo p q) := by
    have := (f.injective.injOn (s := Set.Ioo p q)).bijOn_image
    rwa [f.image_Ioo, hp, hq] at this
  have hperm : ∑ᶠ y ∈ Set.Ioo p q, φ (f y) = ∑ᶠ y ∈ Set.Ioo p q, φ y :=
    finsum_mem_eq_of_bijOn f hbij (fun _ _ => rfl)
  have hsum : ∑ᶠ y ∈ Set.Ioo p q, φ (f y) =
      ∑ᶠ y ∈ Set.Ioo p q, jumpFun f y + ∑ᶠ y ∈ Set.Ioo p q, φ y := by
    rw [← finsum_mem_add_distrib' (hfinJ _) (hfinφ _)]
    exact finsum_mem_congr rfl (fun y _ => by rw [hrel y]; ring)
  unfold jsum
  rw [hperm] at hsum
  omega

/-! ### A maximal interval of moved points -/

theorem exists_component_pos (E : ℝ ≃o ℝ) (h0 : E 0 = 0) (h1 : E 1 = 1) {z0 : ℝ}
    (hz0 : 0 ≤ z0) (hz1 : z0 ≤ 1) (hlt : z0 < E z0) :
    ∃ p q : ℝ, 0 ≤ p ∧ p < q ∧ q ≤ 1 ∧ E p = p ∧ E q = q ∧
      ∀ z, p < z → z < q → z < E z := by
  have hc : Continuous E := E.continuous
  have hclosed : IsClosed {t : ℝ | E t ≤ t} := isClosed_le hc continuous_id
  have hclosed' : IsClosed {t : ℝ | t ≤ E t} := isClosed_le continuous_id hc
  -- the left end
  set S1 : Set ℝ := Set.Icc 0 z0 ∩ {t : ℝ | E t ≤ t} with hS1
  have hS1c : IsClosed S1 := isClosed_Icc.inter hclosed
  have hS1ne : S1.Nonempty := ⟨0, ⟨le_rfl, hz0⟩, by simp [h0]⟩
  have hS1b : BddAbove S1 := ⟨z0, fun t ht => ht.1.2⟩
  have hp : sSup S1 ∈ S1 := hS1c.csSup_mem hS1ne hS1b
  set p := sSup S1 with hpdef
  have hpz : p < z0 := by
    refine lt_of_le_of_ne hp.1.2 (fun he => ?_)
    have h2 : E p ≤ p := hp.2
    rw [he] at h2
    linarith
  have hR : ∀ z, p < z → z ≤ z0 → z < E z := by
    intro z hpz' hzz
    by_contra hle
    push Not at hle
    have hmem : z ∈ S1 := ⟨⟨le_trans hp.1.1 hpz'.le, hzz⟩, hle⟩
    have := le_csSup hS1b hmem
    linarith
  have hEp : E p = p := by
    apply le_antisymm hp.2
    have hsub : Set.Ioc p z0 ⊆ {t | t ≤ E t} := fun z hz => (hR z hz.1 hz.2).le
    have := closure_minimal hsub hclosed'
    rw [closure_Ioc hpz.ne] at this
    exact this ⟨le_rfl, hpz.le⟩
  -- the right end
  set S2 : Set ℝ := Set.Icc z0 1 ∩ {t : ℝ | E t ≤ t} with hS2
  have hS2c : IsClosed S2 := isClosed_Icc.inter hclosed
  have hS2ne : S2.Nonempty := ⟨1, ⟨hz1, le_rfl⟩, by simp [h1]⟩
  have hS2b : BddBelow S2 := ⟨z0, fun t ht => ht.1.1⟩
  have hq : sInf S2 ∈ S2 := hS2c.csInf_mem hS2ne hS2b
  set q := sInf S2 with hqdef
  have hzq : z0 < q := by
    refine lt_of_le_of_ne hq.1.1 (fun he => ?_)
    have h2 : E q ≤ q := hq.2
    rw [← he] at h2
    linarith
  have hL : ∀ z, z0 ≤ z → z < q → z < E z := by
    intro z hzz hzq'
    by_contra hle
    push Not at hle
    have hmem : z ∈ S2 := ⟨⟨hzz, le_trans hzq'.le hq.1.2⟩, hle⟩
    have := csInf_le hS2b hmem
    linarith
  have hEq : E q = q := by
    apply le_antisymm hq.2
    have hsub : Set.Ico z0 q ⊆ {t | t ≤ E t} := fun z hz => (hL z hz.1 hz.2).le
    have := closure_minimal hsub hclosed'
    rw [closure_Ico hzq.ne] at this
    exact this ⟨hzq.le, le_rfl⟩
  refine ⟨p, q, hp.1.1, by linarith, hq.1.2, hEp, hEq, fun z hz1' hz2' => ?_⟩
  rcases le_total z z0 with hz | hz
  · exact hR z hz1' hz
  · exact hL z hz hz2'

theorem exists_component (E : ℝ ≃o ℝ) (h0 : E 0 = 0) (h1 : E 1 = 1) {z0 : ℝ}
    (hz0 : 0 ≤ z0) (hz1 : z0 ≤ 1) (hne : E z0 ≠ z0) :
    ∃ p q : ℝ, 0 ≤ p ∧ p < q ∧ q ≤ 1 ∧ E p = p ∧ E q = q ∧
      ((∀ z, p < z → z < q → z < E z) ∨ (∀ z, p < z → z < q → E z < z)) := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `E z0 < z0`: apply the positive case to `E.symm` at `E z0`
    have hs0 : E.symm 0 = 0 := by rw [E.symm_apply_eq, h0]
    have hs1 : E.symm 1 = 1 := by rw [E.symm_apply_eq, h1]
    have hw0 : 0 ≤ E z0 := by rw [← h0]; exact E.monotone hz0
    have hw1 : E z0 ≤ 1 := by rw [← h1]; exact E.monotone hz1
    have hw : E z0 < E.symm (E z0) := by rw [E.symm_apply_apply]; exact hlt
    obtain ⟨p, q, hp0, hpq, hq1, hEp, hEq, hR⟩ := exists_component_pos E.symm hs0 hs1 hw0 hw1 hw
    have hEp' : E p = p := by
      have := congrArg E hEp
      rwa [E.apply_symm_apply, eq_comm] at this
    have hEq' : E q = q := by
      have := congrArg E hEq
      rwa [E.apply_symm_apply, eq_comm] at this
    refine ⟨p, q, hp0, hpq, hq1, hEp', hEq', Or.inr fun z hpz hzq => ?_⟩
    have h1' : p < E z := by rw [← hEp']; exact E.strictMono hpz
    have h2' : E z < q := by rw [← hEq']; exact E.strictMono hzq
    have := hR (E z) h1' h2'
    rwa [E.symm_apply_apply] at this
  · obtain ⟨p, q, hp0, hpq, hq1, hEp, hEq, hR⟩ := exists_component_pos E h0 h1 hz0 hz1 hlt
    exact ⟨p, q, hp0, hpq, hq1, hEp, hEq, Or.inl hR⟩

/-! ### Fixing the endpoints -/

theorem apply_zero (f : UI ≃o UI) : (f ⟨0, zero_mem_UI⟩ : ℝ) = 0 := by
  apply le_antisymm _ (f _).2.1
  have hle : (⟨0, zero_mem_UI⟩ : UI) ≤ f.symm ⟨0, zero_mem_UI⟩ := (f.symm _).2.1
  have := f.monotone hle
  rw [f.apply_symm_apply] at this
  exact this

theorem apply_one (f : UI ≃o UI) : (f ⟨1, one_mem_UI⟩ : ℝ) = 1 := by
  apply le_antisymm (f _).2.2
  have hle : f.symm ⟨1, one_mem_UI⟩ ≤ (⟨1, one_mem_UI⟩ : UI) := (f.symm _).2.2
  have := f.monotone hle
  rw [f.apply_symm_apply] at this
  exact this

/-! ### Freeness -/

theorem cocycle_free (g : F) (φ : UI →₀ ℤ)
    (h : cocycle g + Finsupp.mapDomain (fun x => g • x) φ = φ) : g = 1 := by
  set f : UI ≃o UI := (g : UI ≃o UI) with hfdef
  have hf : f ∈ F := g.2
  by_contra hg1
  obtain ⟨z0, hz0⟩ : ∃ z0 : UI, f z0 ≠ z0 := by
    by_contra hall
    push Not at hall
    apply hg1
    apply Subtype.ext
    ext x
    rw [show (g : UI ≃o UI) x = x from hall x]
    simp
  set E : ℝ ≃o ℝ := extend f with hE
  have hEz : ∀ z : UI, E z = (f z : ℝ) := fun z => by
    simp only [E, extend_apply]
    exact extendFun_of_mem f z.2
  have hE0 : E 0 = 0 := by
    rw [show (0:ℝ) = ((⟨0, zero_mem_UI⟩ : UI) : ℝ) from rfl, hEz]; exact apply_zero f
  have hE1 : E 1 = 1 := by
    rw [show (1:ℝ) = ((⟨1, one_mem_UI⟩ : UI) : ℝ) from rfl, hEz]; exact apply_one f
  have hEne : E z0 ≠ z0 := by
    rw [hEz]; intro he; exact hz0 (Subtype.ext he)
  obtain ⟨p, q, hp0, hpq, hq1, hEp, hEq, hsign⟩ := exists_component E hE0 hE1 z0.2.1 z0.2.2 hEne
  set pU : UI := ⟨p, hp0, by linarith⟩ with hpU
  set qU : UI := ⟨q, by linarith, hq1⟩ with hqU
  have hfp : f pU = pU := Subtype.ext (by rw [← hEz]; exact hEp)
  have hfq : f qU = qU := Subtype.ext (by rw [← hEz]; exact hEq)
  -- the slope exponents at the two ends agree
  have hjs := jsum_eq_zero_of_cocycle g φ h hfp hfq
  rw [jsum_eq hf (show pU < qU from hpq)] at hjs
  have hn : lexp f qU = rexp f pU := by omega
  set n := rexp f pU with hndef
  obtain ⟨c, δ, hδ, hr⟩ := rexp_spec hf (show (pU:ℝ) < 1 by simp [pU]; linarith)
  obtain ⟨c', δ', hδ', hl⟩ := lexp_spec hf (show 0 < (qU:ℝ) by simp [qU]; linarith)
  rw [hn] at hl
  -- a point just right of `p` and a point just left of `q`
  set z1 : ℝ := p + min δ ((q - p) / 2) with hz1
  set z2 : ℝ := q - min δ' ((q - p) / 2) with hz2
  have hm1 : 0 < min δ ((q - p) / 2) := lt_min hδ (by linarith)
  have hm1' : min δ ((q - p) / 2) ≤ δ := min_le_left _ _
  have hm1'' : min δ ((q - p) / 2) ≤ (q - p) / 2 := min_le_right _ _
  have hm2 : 0 < min δ' ((q - p) / 2) := lt_min hδ' (by linarith)
  have hm2' : min δ' ((q - p) / 2) ≤ δ' := min_le_left _ _
  have hm2'' : min δ' ((q - p) / 2) ≤ (q - p) / 2 := min_le_right _ _
  have hz1I : z1 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hz2I : z2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have ep : (p:ℝ) = 2 ^ n * p + c := by
    have := hr pU le_rfl (by simp [pU]; linarith)
    rw [hfp] at this; exact this
  have eq' : (q:ℝ) = 2 ^ n * q + c' := by
    have := hl qU (by simp [qU]; linarith) le_rfl
    rw [hfq] at this; exact this
  have e1 : (f ⟨z1, hz1I⟩ : ℝ) = 2 ^ n * z1 + c :=
    hr ⟨z1, hz1I⟩ (by simp [pU]; linarith) (by simp [pU]; linarith)
  have e2 : (f ⟨z2, hz2I⟩ : ℝ) = 2 ^ n * z2 + c' :=
    hl ⟨z2, hz2I⟩ (by simp [qU]; linarith) (by simp [qU]; linarith)
  have d1 : E z1 - z1 = (2 ^ n - 1) * (z1 - p) := by
    rw [show z1 = ((⟨z1, hz1I⟩ : UI) : ℝ) from rfl, hEz]
    linear_combination e1 - ep
  have d2 : E z2 - z2 = (2 ^ n - 1) * (z2 - q) := by
    rw [show z2 = ((⟨z2, hz2I⟩ : UI) : ℝ) from rfl, hEz]
    linear_combination e2 - eq'
  have hu : 0 < z1 - p := by linarith
  have hv : z2 - q < 0 := by linarith
  have hz1pq : p < z1 ∧ z1 < q := ⟨by linarith, by linarith⟩
  have hz2pq : p < z2 ∧ z2 < q := ⟨by linarith, by linarith⟩
  rcases hsign with hpos | hneg
  · have k1 : 0 < (2 ^ n - 1) * (z1 - p) := by rw [← d1]; linarith [hpos z1 hz1pq.1 hz1pq.2]
    have k2 : 0 < (2 ^ n - 1) * (z2 - q) := by rw [← d2]; linarith [hpos z2 hz2pq.1 hz2pq.2]
    nlinarith [mul_pos k1 (neg_pos.2 hv), mul_pos k2 hu]
  · have k1 : (2 ^ n - 1) * (z1 - p) < 0 := by rw [← d1]; linarith [hneg z1 hz1pq.1 hz1pq.2]
    have k2 : (2 ^ n - 1) * (z2 - q) < 0 := by rw [← d2]; linarith [hneg z2 hz2pq.1 hz2pq.2]
    nlinarith [mul_pos_of_neg_of_neg k1 hv, mul_neg_of_neg_of_pos k2 hu]

end FAmenChild.PartC2
