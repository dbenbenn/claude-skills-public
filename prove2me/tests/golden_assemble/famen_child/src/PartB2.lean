import Solutions.FAmenChild.Blueprint
import Theorems.Thm_Garrido_isAmenable_of_commGroup

/-!
# Part B2: symmetric translation-invariant means on finitely supported `ℤ`-functions
-/

open scoped ENNReal Pointwise

namespace FAmenChild.PartB2

/-- Right composition with a permutation is injective. -/
lemma comp_perm_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun w : Fin n → ℤ => w ∘ σ) := by
  intro a b h
  funext i
  have := congrFun h (σ.symm i)
  simpa using this

/-- Right composition with a permutation is surjective. -/
lemma comp_perm_surjective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Surjective (fun w : Fin n → ℤ => w ∘ σ) := by
  intro w
  exact ⟨w ∘ σ.symm, by funext i; simp⟩

theorem exists_symMean (n : ℕ) : ∃ μ : Set (Fin n → ℤ) → ℝ≥0∞,
    Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1 ∧
    (∀ (v : Fin n → ℤ) (S : Set (Fin n → ℤ)), μ ((v + ·) '' S) = μ S) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (S : Set (Fin n → ℤ)), μ ((fun w => w ∘ σ) '' S) = μ S) := by
  obtain ⟨m, hm, h1, hinv⟩ := Garrido.isAmenable_of_commGroup (Multiplicative (Fin n → ℤ))
  -- transport to `Fin n → ℤ`
  set m' : Set (Fin n → ℤ) → ℝ≥0∞ := fun S => m (Multiplicative.toAdd ⁻¹' S) with hm'def
  have hm'0 : m' ∅ = 0 := by simp [hm'def, hm.1]
  have hm'add : ∀ s t : Set (Fin n → ℤ), Disjoint s t → m' (s ∪ t) = m' s + m' t := by
    intro s t hst
    simp only [hm'def, Set.preimage_union]
    exact hm.2 _ _ (hst.preimage _)
  have hm'1 : m' Set.univ = 1 := by simp [hm'def, h1]
  have hm'tr : ∀ (v : Fin n → ℤ) (S : Set (Fin n → ℤ)), m' ((v + ·) '' S) = m' S := by
    intro v S
    have key : Multiplicative.toAdd ⁻¹' ((v + ·) '' S) =
        Multiplicative.ofAdd v • (Multiplicative.toAdd ⁻¹' S) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_smul_set, smul_eq_mul]
      constructor
      · rintro ⟨s, hs, hsg⟩
        refine ⟨Multiplicative.ofAdd s, by simpa using hs, ?_⟩
        rw [← ofAdd_add, hsg, ofAdd_toAdd]
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Multiplicative.toAdd y, hy, by simp⟩
    simp only [hm'def]
    rw [key, hinv]
  -- symmetrise
  set c : ℝ≥0∞ := ((Fintype.card (Equiv.Perm (Fin n)) : ℕ) : ℝ≥0∞)⁻¹ with hc
  refine ⟨fun S => c * ∑ σ : Equiv.Perm (Fin n), m' ((fun w => w ∘ σ) '' S), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [hm'0]
  · intro s t hst
    simp only [Set.image_union]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact hm'add _ _ ((Set.disjoint_image_iff (comp_perm_injective σ)).mpr hst)
  · simp only [Set.image_univ_of_surjective (comp_perm_surjective _), hm'1, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, hc]
    exact ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)
  · intro v S
    simp only
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    have : (fun w : Fin n → ℤ => w ∘ σ) '' ((v + ·) '' S) =
        ((v ∘ σ) + ·) '' ((fun w : Fin n → ℤ => w ∘ σ) '' S) := by
      simp only [Set.image_image]
      rfl
    rw [this, hm'tr]
  · intro τ S
    simp only
    congr 1
    have : ∀ σ : Equiv.Perm (Fin n), (fun w : Fin n → ℤ => w ∘ σ) '' ((fun w => w ∘ τ) '' S) =
        (fun w : Fin n → ℤ => w ∘ (Equiv.mulLeft τ σ)) '' S := by
      intro σ
      simp only [Set.image_image, Equiv.coe_mulLeft, Equiv.Perm.coe_mul]
      rfl
    simp only [this]
    exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => m' ((fun w : Fin n → ℤ => w ∘ σ) '' S))

/-! ## `meanOn` -/

section B2
variable {X : Type*}

lemma symMean_spec (n : ℕ) :
    Garrido.IsFinitelyAdditiveMeasure (symMean n) ∧ symMean n Set.univ = 1 ∧
    (∀ (v : Fin n → ℤ) (S : Set (Fin n → ℤ)), symMean n ((v + ·) '' S) = symMean n S) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (S : Set (Fin n → ℤ)),
      symMean n ((fun w => w ∘ σ) '' S) = symMean n S) :=
  (FAmenChild.exists_symMean n).choose_spec

lemma meanOn_eq (A : Finset X) (S : Set (X →₀ ℤ)) :
    meanOn A S = symMean A.card (extendFin A ⁻¹' S) := rfl

lemma extendFin_apply (A : Finset X) (w : Fin A.card → ℤ) (x : X) :
    extendFin A w x = open Classical in if h : x ∈ A then w (A.equivFin ⟨x, h⟩) else 0 := by
  simp [extendFin, Finsupp.onFinset_apply]

lemma extendFin_add (A : Finset X) (u v : Fin A.card → ℤ) :
    extendFin A (u + v) = extendFin A u + extendFin A v := by
  ext x
  simp only [extendFin_apply, Finsupp.coe_add, Pi.add_apply]
  split_ifs <;> simp

lemma extendFin_neg (A : Finset X) (u : Fin A.card → ℤ) :
    extendFin A (-u) = -extendFin A u := by
  ext x
  simp only [extendFin_apply, Finsupp.coe_neg, Pi.neg_apply]
  split_ifs <;> simp

lemma extendFin_restrict (A : Finset X) (w : X →₀ ℤ) (hw : (↑w.support : Set X) ⊆ ↑A) :
    extendFin A (fun i => w (A.equivFin.symm i)) = w := by
  ext x
  rw [extendFin_apply]
  split_ifs with h
  · simp
  · have : x ∉ w.support := fun hx => h (hw hx)
    simp only [Finsupp.mem_support_iff, not_not] at this
    exact this.symm

/-- Right composition with an equivalence, as a preimage, symmetrises away. -/
lemma symMean_preimage_comp (k l : ℕ) (τ : Fin k ≃ Fin l) (T : Set (Fin k → ℤ)) :
    symMean l ((fun w : Fin l → ℤ => w ∘ τ) ⁻¹' T) = symMean k T := by
  obtain rfl : k = l := by simpa using Fintype.card_congr τ
  have : (fun w : Fin k → ℤ => w ∘ τ) ⁻¹' T = (fun w : Fin k → ℤ => w ∘ τ.symm) '' T := by
    ext w
    constructor
    · intro h
      exact ⟨w ∘ τ, h, by funext i; simp⟩
    · rintro ⟨u, hu, rfl⟩
      simpa [Set.mem_preimage, Function.comp_def] using hu
  rw [this]
  exact (symMean_spec k).2.2.2 τ.symm T

theorem meanOn_isFinitelyAdditiveMeasure (A : Finset X) :
    Garrido.IsFinitelyAdditiveMeasure (meanOn A) ∧ meanOn A Set.univ = 1 := by
  obtain ⟨⟨h0, hadd⟩, h1, -, -⟩ := symMean_spec A.card
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [meanOn_eq] using h0
  · intro s t hst
    simp only [meanOn_eq, Set.preimage_union]
    exact hadd _ _ (hst.preimage _)
  · simpa [meanOn_eq] using h1

theorem meanOn_add (A : Finset X) (w : X →₀ ℤ) (hw : (↑w.support : Set X) ⊆ ↑A)
    (S : Set (X →₀ ℤ)) : meanOn A ((w + ·) '' S) = meanOn A S := by
  set w₀ : Fin A.card → ℤ := fun i => w (A.equivFin.symm i) with hw₀
  have hext : extendFin A w₀ = w := extendFin_restrict A w hw
  have key : extendFin A ⁻¹' ((w + ·) '' S) = (w₀ + ·) '' (extendFin A ⁻¹' S) := by
    rw [Set.image_add_left, Set.image_add_left, ← Set.preimage_comp, ← Set.preimage_comp]
    congr 1
    funext u
    simp only [Function.comp_apply]
    rw [extendFin_add, extendFin_neg, hext]
  rw [meanOn_eq, meanOn_eq, key]
  exact (symMean_spec A.card).2.2.1 w₀ _

theorem meanOn_perm (σ : Equiv.Perm X) (A : Finset X) (S : Set (X →₀ ℤ)) :
    meanOn (A.map σ.toEmbedding) ((Finsupp.mapDomain σ) '' S) = meanOn A S := by
  set B := A.map σ.toEmbedding with hB
  have hmem : ∀ x, x ∈ A ↔ σ x ∈ B := fun x => by
    simp [hB]
  let e : A ≃ B := σ.subtypeEquiv hmem
  let τ : Fin A.card ≃ Fin B.card := A.equivFin.symm.trans (e.trans B.equivFin)
  have hτ : ∀ x (h : x ∈ A), τ (A.equivFin ⟨x, h⟩) = B.equivFin ⟨σ x, (hmem x).1 h⟩ := by
    intro x h
    simp [τ, e]
  have hid : ∀ w : Fin B.card → ℤ,
      extendFin B w = Finsupp.mapDomain σ (extendFin A (w ∘ τ)) := by
    intro w
    ext y
    obtain ⟨x, rfl⟩ := σ.surjective y
    rw [Finsupp.mapDomain_apply σ.injective, extendFin_apply, extendFin_apply]
    by_cases h : x ∈ A
    · rw [dif_pos h, dif_pos ((hmem x).1 h), Function.comp_apply, hτ x h]
    · rw [dif_neg h, dif_neg (fun h' => h ((hmem x).2 h'))]
  have key : extendFin B ⁻¹' ((Finsupp.mapDomain σ) '' S) =
      (fun w : Fin B.card → ℤ => w ∘ τ) ⁻¹' (extendFin A ⁻¹' S) := by
    ext w
    simp only [Set.mem_preimage, hid w]
    exact (Finsupp.mapDomain_injective σ.injective).mem_set_image
  rw [meanOn_eq, meanOn_eq, key]
  exact symMean_preimage_comp A.card B.card τ _

end B2

end FAmenChild.PartB2
