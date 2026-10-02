import Solutions.FAmenChild.Blueprint

/-!
# Part B3: the mean on `X →₀ ℤ` from extensive amenability

`μ S = ofReal (∫ (meanOn A S).toReal dm(A))`, integrating the symmetric means `meanOn A` of
Part B2 against the extensively amenable mean `m` on `Finset X`, with the integral of Part B1.
-/

open scoped ENNReal Pointwise

namespace FAmenChild.PartB3

lemma fam_mono {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    {s t : Set α} (hst : s ⊆ t) : m s ≤ m t := by
  have := hm.2 s (t \ s) disjoint_sdiff_self_right
  rw [Set.union_sdiff_cancel hst] at this
  rw [this]
  exact le_self_add

lemma fam_le_one {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    (h1 : m Set.univ = 1) (s : Set α) : m s ≤ 1 :=
  h1 ▸ fam_mono hm (Set.subset_univ s)

lemma fam_compl_eq_zero {α : Type*} {m : Set α → ℝ≥0∞}
    (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) {s : Set α}
    (hs : m s = 1) : m sᶜ = 0 := by
  have := hm.2 s sᶜ disjoint_compl_right
  rw [Set.union_compl_self, h1, hs] at this
  have h' : (1 : ℝ≥0∞) + m sᶜ = 1 + 0 := by rw [← this, add_zero]
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h'

lemma meanOn_le_one {X : Type*} (A : Finset X) (S : Set (X →₀ ℤ)) : meanOn A S ≤ 1 :=
  fam_le_one (meanOn_isFinitelyAdditiveMeasure A).1 (meanOn_isFinitelyAdditiveMeasure A).2 S

lemma meanOn_ne_top {X : Type*} (A : Finset X) (S : Set (X →₀ ℤ)) : meanOn A S ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (meanOn_le_one A S)

theorem exists_affine_mean {G X : Type*} [Group G] [MulAction G X] (Y : Set X)
    (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) :
    ∃ μ : Set (X →₀ ℤ) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1 ∧
      (∀ (g : G) (S : Set (X →₀ ℤ)), μ ((Finsupp.mapDomain (fun x => g • x)) '' S) = μ S) ∧
      (∀ w : X →₀ ℤ, (↑w.support : Set X) ⊆ Y → ∀ S, μ ((w + ·) '' S) = μ S) := by
  obtain ⟨m, hm, -, h1, hinv, hfull⟩ := h
  refine ⟨fun S => ENNReal.ofReal (integ m (fun A => (meanOn A S).toReal)), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `μ ∅ = 0`
    have h0 : (fun A : Finset X => (meanOn A (∅ : Set (X →₀ ℤ))).toReal)
        = (∅ : Set (Finset X)).indicator 1 := by
      funext A
      rw [(meanOn_isFinitelyAdditiveMeasure A).1.1, Set.indicator_empty]
      rfl
    simp only
    rw [h0, integ_indicator hm h1, hm.1]
    simp
  · -- finite additivity
    intro s t hst
    have hadd : ∀ A : Finset X, meanOn A (s ∪ t) = meanOn A s + meanOn A t :=
      fun A => (meanOn_isFinitelyAdditiveMeasure A).1.2 s t hst
    have hfun : (fun A : Finset X => (meanOn A (s ∪ t)).toReal)
        = (fun A => (meanOn A s).toReal) + (fun A => (meanOn A t).toReal) := by
      funext A
      rw [hadd A, Pi.add_apply, ENNReal.toReal_add (meanOn_ne_top A s) (meanOn_ne_top A t)]
    have hle : ∀ A : Finset X, (meanOn A s).toReal + (meanOn A t).toReal ≤ 1 := by
      intro A
      rw [← ENNReal.toReal_add (meanOn_ne_top A s) (meanOn_ne_top A t), ← hadd A]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact meanOn_le_one A _)
    have hf0 : ∀ A : Finset X, 0 ≤ (meanOn A s).toReal := fun A => ENNReal.toReal_nonneg
    have hg0 : ∀ A : Finset X, 0 ≤ (meanOn A t).toReal := fun A => ENNReal.toReal_nonneg
    have hf1 : ∀ A : Finset X, (meanOn A s).toReal ≤ 1 := fun A =>
      le_trans (le_add_of_nonneg_right (hg0 A)) (hle A)
    have hg1 : ∀ A : Finset X, (meanOn A t).toReal ≤ 1 := fun A =>
      le_trans (le_add_of_nonneg_left (hf0 A)) (hle A)
    simp only
    rw [hfun, integ_add hm h1 hf0 hg0 hle,
      ENNReal.ofReal_add (integ_nonneg_le_one hm h1 hf0 hf1).1
        (integ_nonneg_le_one hm h1 hg0 hg1).1]
  · -- `μ univ = 1`
    have hu : (fun A : Finset X => (meanOn A (Set.univ : Set (X →₀ ℤ))).toReal)
        = (Set.univ : Set (Finset X)).indicator 1 := by
      funext A
      rw [(meanOn_isFinitelyAdditiveMeasure A).2, Set.indicator_univ]
      rfl
    simp only
    rw [hu, integ_indicator hm h1, h1]
    simp
  · -- invariance under the linear action of `G`
    intro g S
    simp only
    congr 1
    let τ : Finset X ≃ Finset X := (MulAction.toPerm g⁻¹ : Equiv.Perm X).finsetCongr
    have hτ : ∀ T : Set (Finset X), m (τ '' T) = m T := fun T => hinv g⁻¹ T
    have hfun : (fun A : Finset X => (meanOn A (Finsupp.mapDomain (fun x => g • x) '' S)).toReal)
        = (fun A : Finset X => (meanOn A S).toReal) ∘ τ := by
      funext A
      have key := meanOn_perm (MulAction.toPerm g) (A.map (MulAction.toPerm g⁻¹).toEmbedding) S
      have hA : (A.map (MulAction.toPerm g⁻¹ : Equiv.Perm X).toEmbedding).map
          (MulAction.toPerm g : Equiv.Perm X).toEmbedding = A := by
        rw [Finset.map_map]
        ext x
        simp
      rw [hA] at key
      exact congrArg ENNReal.toReal key
    rw [hfun, integ_comp_equiv τ hτ]
  · -- invariance under translations supported in `Y`
    intro w hw S
    simp only
    congr 1
    apply integ_congr hm h1
    have hsub : {A : Finset X | (meanOn A ((w + ·) '' S)).toReal ≠ (meanOn A S).toReal}
        ⊆ {A : Finset X | w.support ⊆ A}ᶜ := by
      intro A hA hwA
      apply hA
      rw [meanOn_add A w (by exact_mod_cast hwA) S]
    have hc : m {A : Finset X | w.support ⊆ A}ᶜ = 0 :=
      fam_compl_eq_zero hm h1 (hfull w.support hw)
    exact le_antisymm (hc ▸ fam_mono hm hsub) bot_le

end FAmenChild.PartB3
