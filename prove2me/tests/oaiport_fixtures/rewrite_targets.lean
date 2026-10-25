open Finset MeasureTheory

-- each example is written as OpenAI's Mathlib (d13f23b) accepts it; core_rewrites and the compat
-- block turn it into what ours accepts

example (s t : Set ℕ) (h : s = t) : s ≃ t := Set.equivOfEq h

example (μ : YoungDiagram) : μ.transpose.card = μ.card := by simp

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure (α × β))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (μ.map Prod.fst) := inferInstance

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure (α × β))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (μ.map Prod.snd) := inferInstance

example {α : Type*} [MeasurableSpace α] {p : α → Prop} (μ : Measure {a // p a})
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (μ.map Subtype.val) := inferInstance

example (s s' : ℕ →₀ ℕ) (a b : ℚ) :
    MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul_monomial

example {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a b : A}
    (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha

example {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M] (f : ℕ → M) (s : Finset ℕ)
    (hf : ∀ i ∈ s, 1 ≤ f i) {i : ℕ} (hi : i ∈ s) : f i ≤ ∏ j ∈ s, f j :=
  Finset.single_le_prod hf hi

example {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M] (f : ℕ → M) (s t : Finset ℕ)
    (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) : ∏ j ∈ s, f j ≤ ∏ j ∈ t, f j :=
  Finset.prod_le_prod_of_subset_of_one_le h hf

example (c : ENNReal) (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (c • μ).map f = c • μ.map f := by
  rw [Measure.map_smul _ hf.aemeasurable]

example (L : AddSubgroup ℝ) [DiscreteTopology L] : IsClosed (L : Set ℝ) :=
  AddSubgroup.isClosed_of_discreteTopology (U := L)

example (f : ℕ → ℕ) (hf : Function.Injective f) (v : ℕ →₀ ℕ) (x : ℕ) :
    Finsupp.mapDomain f v (f x) = v x := Finsupp.mapDomain_apply_of_injective hf v x
