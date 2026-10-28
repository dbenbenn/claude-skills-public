/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
/-- Mathlib d13f23b's `LipschitzOnWith.comp_absolutelyContinuousOnInterval`: a Lipschitz function of an
absolutely continuous one is absolutely continuous (Boltzmann EntropyIntegralBalance and JetSupersolutions,
oaiq-080). -/
theorem _root_.LipschitzOnWith.comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {s : Set ℝ} {K : NNReal}
    {a b : ℝ} (hg : LipschitzOnWith K g s) (hmaps : ∀ t ∈ Set.uIcc a b, f t ∈ s)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  have h0 := hf
  unfold AbsolutelyContinuousOnInterval at h0 ⊢
  have h1 := h0.const_mul (K : ℝ)
  rw [mul_zero] at h1
  refine squeeze_zero' ?_ ?_ h1
  · exact Filter.Eventually.of_forall (fun E => Finset.sum_nonneg (fun i _ => dist_nonneg))
  · refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall (fun E hE => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' := hE.left i hi
    have := hg (hmaps _ hi'.left) (hmaps _ hi'.right)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) this
    rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist, ENNReal.coe_toReal] at h2
/-- The `LipschitzWith` form of the previous lemma (JetSupersolutions, oaiq-080). -/
theorem _root_.LipschitzWith.comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {K : NNReal}
    {a b : ℝ} (hg : LipschitzWith K g) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b :=
  (hg.lipschitzOnWith (s := Set.univ)).comp_absolutelyContinuousOnInterval (fun _ _ => Set.mem_univ _) hf
/-- Mathlib d13f23b's `Finset.equivOfEq`: the equivalence between the subtypes of equal finsets
(Coboundary CongruenceFrames, 2026-10-26). -/
def _root_.Finset.equivOfEq {α : Type*} {s t : Finset α} (h : s = t) : s ≃ t :=
  Equiv.subtypeEquivRight (fun _ => by rw [h])
/-- Mathlib d13f23b's `Finsupp.mapDomain_fintype`: on a finite index type `mapDomain f v` is the
sum of the point masses at the images (Thomason Polyhedra, oaiq-043). -/
theorem _root_.Finsupp.mapDomain_fintype {α β M : Type*} [Fintype α] [AddCommMonoid M]
    (f : α → β) (v : α →₀ M) : Finsupp.mapDomain f v = ∑ i, Finsupp.single (f i) (v i) := by
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp)]

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- The `mpr` direction of Mathlib d13f23b's `unifIntegrable_iff`, whose `UnifIntegrable` takes
extended-real `ε` and `δ` and bounds `eLpNorm (f i) p (μ.restrict s)`; ours takes real ones and a
measurable set `s` (SLE IntegralLimits, oaiq-027). -/
theorem unifIntegrable_of_enn {α β ι : Type*} {m : MeasurableSpace α} [NormedAddCommGroup β]
    {f : ι → α → β} {p : ENNReal} {μ : MeasureTheory.Measure α}
    (h : ∀ ε : ENNReal, 0 < ε → ∃ δ : ENNReal, 0 < δ ∧
      ∀ i s, μ s ≤ δ → MeasureTheory.eLpNorm (f i) p (μ.restrict s) ≤ ε) :
    MeasureTheory.UnifIntegrable f p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min δ 1).toReal, ENNReal.toReal_pos (lt_min hδ one_pos).ne' hne,
    fun i s hsm hs => ?_⟩
  rw [MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hsm]
  refine hb i s (hs.trans ?_)
  rw [ENNReal.ofReal_toReal hne]
  exact min_le_left _ _
/-- Mathlib d13f23b's `Measure.isProbabilityMeasure_of_map`, which takes the map's measurability; ours takes
the function `f`, and `_` there leaves the instance argument stuck (HardSphere, oaiq-054). -/
theorem isProbabilityMeasure_of_map_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {f : α → β} [MeasureTheory.IsProbabilityMeasure (μ.map f)]
    (_hf : AEMeasurable f μ) : MeasureTheory.IsProbabilityMeasure μ :=
  MeasureTheory.Measure.isProbabilityMeasure_of_map f
/-- Mathlib d13f23b's `FiniteMeasure.mass_map_le`, which takes the map's measurability; ours takes `f` and
`μ`, and `_ _` there leaves `f` undetermined (BalancedRyser, oaiq-063). -/
theorem finiteMeasure_mass_map_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {f : Ω → Ω'} {μ : MeasureTheory.FiniteMeasure Ω} (_hf : AEMeasurable f (μ : MeasureTheory.Measure Ω)) :
    (μ.map f).mass ≤ μ.mass :=
  MeasureTheory.FiniteMeasure.mass_map_le f μ
/-- Mathlib d13f23b's `lintegral_map_le f (hg : AEMeasurable g μ)`; ours is `lintegral_map_le f g` (CoulombAtom,
oaiq-071). -/
theorem lintegral_map_le_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    (f : β → ENNReal) {g : α → β} (_hg : AEMeasurable g μ) :
    ∫⁻ a, f a ∂MeasureTheory.Measure.map g μ ≤ ∫⁻ a, f (g a) ∂μ :=
  MeasureTheory.lintegral_map_le f g
/-- Mathlib d13f23b's `Measure.lintegral_bind_le f m (hμ : AEMeasurable μ m)`; ours is `lintegral_bind_le f m μ`
(CoulombAtom, oaiq-071). -/
theorem lintegral_bind_le_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (f : β → ENNReal)
    (m : MeasureTheory.Measure α) {μ : α → MeasureTheory.Measure β} (_hμ : AEMeasurable μ m) :
    ∫⁻ x, f x ∂MeasureTheory.Measure.bind m μ ≤ ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  MeasureTheory.Measure.lintegral_bind_le f m μ
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- Mathlib's newer `SimpleGraph.Walk.length_le_bypass_length_iff` (ours has the two directions
separately). `_root_`, so `p.length_le_bypass_length_iff` resolves by dot notation. -/
theorem _root_.SimpleGraph.Walk.length_le_bypass_length_iff {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] {u v : V} (p : G.Walk u v) : p.length ≤ p.bypass.length ↔ p.bypass = p :=
  ⟨p.bypass_eq_self_of_length_le_length_bypass, fun h => by rw [h]⟩
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
/-- Mathlib d13f23b's `spectralRadius_eq_of_unital`: the spectral radius is the supremum of the norms over the spectrum. -/
theorem spectralRadius_eq_of_unital {𝕜 A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] (a : A) :
    spectralRadius 𝕜 a = ⨆ k ∈ spectrum 𝕜 a, (‖k‖₊ : ENNReal) := rfl
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- Mathlib d13f23b's `condDistrib_ae_eq_of_measure_eq_compProd hX hY hκ`; ours takes `X` explicitly and
no `hX` (MultipleMixing Arrays, 2026-10-26). Declared in `OAI`, so a use under `open ProbabilityTheory`
is an overload and the one that typechecks wins. -/
theorem condDistrib_ae_eq_of_measure_eq_compProd
    {Ω β 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β} {m𝓨 : MeasurableSpace 𝓨}
    [StandardBorelSpace 𝓨] [Nonempty 𝓨] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {X : Ω → β} {Y : Ω → 𝓨}
    (_hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {κ : ProbabilityTheory.Kernel β 𝓨} [ProbabilityTheory.IsFiniteKernel κ]
    (hκ : μ.map (fun x => (X x, Y x)) = (μ.map X).compProd κ) :
    ProbabilityTheory.condDistrib Y X μ =ᵐ[μ.map X] κ :=
  ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd X hY hκ
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
/-- d13f23b's `NonUnitalStarRingHom.ofClass`: the bundled hom of a hom class (Kadison commutator
FreeSymmetry10, oaiq-039). `StarRing` rather than bare `Star`, so the `Star` instances agree with those of
`NonUnitalStarRingHom.map_le_map_of_map_star` (MatrixVectorTrace, `CStarMatrix`). -/
def nonUnitalStarRingHomOfClass {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [StarRing R] [StarRing S] [FunLike F R S] [NonUnitalRingHomClass F R S] [StarHomClass F R S] (f : F) :
    R →⋆ₙ+* S :=
  { (f : R →ₙ+* S) with map_star' := map_star f }
/-- d13f23b's `Transcendental.ne_zero`: a transcendental element is nonzero (PiExponent CurveZeroPole,
oaiq-068). -/
theorem _root_.Transcendental.ne_zero {R A : Type*} [CommRing R] [Nontrivial R] [Ring A] [Algebra R A] {x : A}
    (h : Transcendental R x) : x ≠ 0 := fun hx => h (hx ▸ isAlgebraic_zero)
section X
variable {𝕜 𝕜₂ E Eₗ F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [CompleteSpace F]

/-- d13f23b's `LinearMap.extendOfIsometry`: a semilinear map into a complete space that agrees in norm
with a dense-range map `e` extends along `e` to a semilinear isometry. -/
noncomputable def _root_.LinearMap.extendOfIsometry (f : E →ₛₗ[σ] F) {e : E →ₗ[𝕜] Eₗ}
    (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) : Eₗ →ₛₗᵢ[σ] F :=
  { toLinearMap := (f.extendOfNorm e).toLinearMap
    norm_map' := by
      intro x
      refine h_dense.induction_on x (isClosed_eq (by fun_prop) continuous_norm) ?_
      intro y
      have := LinearMap.extendOfNorm_eq (f := f) (e := e) h_dense ⟨1, by simp [h_norm]⟩ y
      simp only [ContinuousLinearMap.coe_coe, this, h_norm] }

omit [RingHomIsometric σ] in
theorem _root_.LinearMap.extendOfIsometry_eq (f : E →ₛₗ[σ] F) {e : E →ₗ[𝕜] Eₗ}
    (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : E) :
    f.extendOfIsometry h_dense h_norm (e x) = f x :=
  LinearMap.extendOfNorm_eq (f := f) (e := e) h_dense ⟨1, by simp [h_norm]⟩ x
end X
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y
/-- d13f23b's `NonUnitalStarAlgHom.map_le_map_iff`: an injective ⋆-homomorphism of non-unital C⋆-algebras
reflects the order (Kadison similarity, oaiq-075). -/
theorem _root_.NonUnitalStarAlgHom.map_le_map_iff {F A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] [PartialOrder A] [StarOrderedRing A] [PartialOrder B]
    [StarOrderedRing B] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (φ : F) (hφ : Function.Injective φ) {a b : A} : φ a ≤ φ b ↔ a ≤ b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← sub_nonneg] at h ⊢
    rw [← map_sub] at h
    generalize b - a = z at h
    have hsa : IsSelfAdjoint z := by
      apply hφ
      rw [map_star]
      exact IsSelfAdjoint.of_nonneg h
    let ψ := Unitization.starMap (φ : A →⋆ₙₐ[ℂ] B)
    have hψ : Function.Injective ψ := Unitization.starMap_injective hφ
    have hz : 0 ≤ (ψ (z : Unitization ℂ A)) := by
      rw [Unitization.starMap_inr]
      exact Unitization.inr_nonneg_iff.mpr h
    have hsa' : IsSelfAdjoint (z : Unitization ℂ A) := hsa.inr ℂ
    rw [← Unitization.inr_nonneg_iff]
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa'] 
    intro x hx
    have := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (hsa'.map ψ)).mp hz
    rw [hsa'.map_spectrum_real ψ hψ] at this
    exact this x hx
  · exact OrderHomClass.mono φ h
/-- d13f23b's `IsSelfAdjoint.norm_le_max_of_le_of_le`: a selfadjoint element squeezed between `a` and `b`
has norm at most `max ‖a‖ ‖b‖` (Kadison similarity, oaiq-075). -/
theorem _root_.IsSelfAdjoint.norm_le_max_of_le_of_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b x : A} (hlo : a ≤ x) (hhi : x ≤ b) (hx : IsSelfAdjoint x) :
    ‖x‖ ≤ max ‖a‖ ‖b‖ := by
  by_cases! nontriv : Nontrivial A
  swap
  · have : x = 0 := Subsingleton.elim _ _
    simp [this]
  have hb : IsSelfAdjoint b := by
    have h1 : IsSelfAdjoint (b - x) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hhi)
    simpa using h1.add hx
  have ha : IsSelfAdjoint a := by
    have h1 : IsSelfAdjoint (x - a) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hlo)
    simpa using hx.sub h1
  have hbx : x ≤ algebraMap ℝ A ‖b‖ := hhi.trans hb.le_algebraMap_norm_self
  have hax : -(algebraMap ℝ A ‖a‖) ≤ x := ha.neg_algebraMap_norm_le_self.trans hlo
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hx with h | h
  · exact ((le_algebraMap_iff_spectrum_le hx).mp hbx _ h).trans (le_max_right _ _)
  · have hax' : algebraMap ℝ A (-‖a‖) ≤ x := by simpa using hax
    have := (algebraMap_le_cfc_iff (R := ℝ) id (-‖a‖) x).mp (by rwa [cfc_id ℝ x hx]) _ h
    simp only [id] at this
    exact (by linarith : ‖x‖ ≤ ‖a‖).trans (le_max_left _ _)
/-- d13f23b's `LinearIsometry.completion`: a linear isometry extends to the completions
(Kadison similarity, oaiq-075). -/
noncomputable def _root_.LinearIsometry.completion {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) :
    UniformSpace.Completion E →ₗᵢ[𝕜] UniformSpace.Completion F :=
  { toLinearMap := f.toContinuousLinearMap.completion.toLinearMap
    norm_map' := by
      intro x
      refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
      intro y
      simp }
@[simp]
theorem _root_.LinearIsometry.completion_apply_coe {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) (x : E) : f.completion (x : UniformSpace.Completion E) = (f x : UniformSpace.Completion F) :=
  ContinuousLinearMap.completion_apply_coe f.toContinuousLinearMap x
/-- Mathlib d13f23b's `Subtype.starOrderedRing`: the order a closed ⋆-subalgebra of a C⋆-algebra inherits
(Kadison similarity, oaiq-075). -/
theorem _root_.Subtype.starOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) [hS : IsClosed (S : Set A)] :
    StarOrderedRing S := by
  refine StarOrderedRing.of_nonneg_iff' (fun {a b} h c => ?_) (fun {s} => ?_)
  · show ((c : A) + (a : A)) ≤ (c : A) + (b : A)
    exact add_le_add le_rfl (show (a : A) ≤ (b : A) from h)
  · constructor
    · intro hs
      have hs' : (0 : A) ≤ (s : A) := hs
      have hmem : CFC.sqrt (s : A) ∈ S := by
        rw [CFC.sqrt_eq_real_sqrt _ hs']
        exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := S) _ s.property
      refine ⟨⟨CFC.sqrt (s : A), hmem⟩, Subtype.ext ?_⟩
      show (s : A) = star (CFC.sqrt (s : A)) * CFC.sqrt (s : A)
      rw [CFC.sqrt_nonneg _ |>.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hs']
    · rintro ⟨t, rfl⟩
      show (0 : A) ≤ star (t : A) * (t : A)
      exact star_mul_self_nonneg _

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed ⋆-subalgebra of a C⋆-algebra is star ordered (d13f23b finds this by instance search). -/
instance starSubalgebraStarOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S :=
  Subtype.starOrderedRing S
instance vonNeumannAlgebraStarOrderedRing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : StarOrderedRing P :=
  Subtype.starOrderedRing P.toStarSubalgebra
open scoped ComplexOrder in
/-- A norm-one functional on a C⋆-algebra with `φ 1 = 1` is monotone; stands in for d13f23b's
`ContinuousLinearMap.monotone_iff_opNorm_eq_map_one` (Kadison similarity, oaiq-075). -/
theorem monotone_of_opNorm_eq_one_of_apply_one {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Nontrivial A] (φ : A →L[ℂ] ℂ) (hn : ‖φ‖ = 1) (h1 : φ 1 = 1) :
    Monotone φ := by
  have hle : ∀ z : A, ‖φ z‖ ≤ ‖z‖ := fun z => by
    simpa [hn] using φ.le_opNorm z
  -- selfadjoint elements have real values
  have him : ∀ h : A, IsSelfAdjoint h → (φ h).im = 0 := by
    intro h hh
    by_contra hy
    set y := (φ h).im with hy_def
    set x := (φ h).re with hx_def
    set C : ℝ := x ^ 2 + y ^ 2 - ‖h‖ ^ 2 with hC
    have hD : 0 < |C| + 1 := by positivity
    set t : ℝ := -y / (|C| + 1) with ht
    set z : A := (1 : A) + ((t : ℂ) * Complex.I) • h with hz
    have hzz : star z * z = (1 : A) + ((t ^ 2 : ℝ) : ℂ) • (h * h) := by
      have hs : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
        simp [Complex.conj_ofReal]
      have ht2 : ((t ^ 2 : ℝ) : ℂ) = -(((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I)) := by
        push_cast; ring_nf; simp [Complex.I_sq]
      rw [ht2]
      simp only [hz, star_add, star_one, star_smul, hh.star_eq, hs, add_mul, mul_add, one_mul, mul_one,
        smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul, smul_neg, neg_mul, smul_add]
      module
    have hnz : ‖z‖ ^ 2 ≤ 1 + t ^ 2 * ‖h‖ ^ 2 := by
      have h0 : ‖z‖ * ‖z‖ = ‖star z * z‖ := (CStarRing.norm_star_mul_self).symm
      rw [sq, h0, hzz]
      calc ‖(1 : A) + ((t ^ 2 : ℝ) : ℂ) • (h * h)‖ ≤ ‖(1 : A)‖ + ‖((t ^ 2 : ℝ) : ℂ) • (h * h)‖ := norm_add_le _ _
        _ ≤ 1 + t ^ 2 * (‖h‖ * ‖h‖) := by
          rw [norm_one, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
          gcongr
          exact norm_mul_le _ _
        _ = 1 + t ^ 2 * ‖h‖ ^ 2 := by ring
    have hphiz : φ z = (1 - t * y : ℝ) + (t * x : ℝ) * Complex.I := by
      have hh' : φ h = (x : ℂ) + (y : ℂ) * Complex.I := (Complex.re_add_im (φ h)).symm
      rw [hz, map_add, map_smul, h1, smul_eq_mul, hh']
      apply Complex.ext <;> simp <;> ring
    have hphin : ‖φ z‖ ^ 2 = (1 - t * y) ^ 2 + (t * x) ^ 2 := by
      rw [hphiz, Complex.sq_norm, Complex.normSq_apply]
      simp; ring
    have hineq : (1 - t * y) ^ 2 + (t * x) ^ 2 ≤ 1 + t ^ 2 * ‖h‖ ^ 2 := by
      rw [← hphin]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hle z) 2).trans hnz
    have hkey : y ^ 2 * (C + 2 * (|C| + 1)) ≤ 0 := by
      have e1 : t * (|C| + 1) = -y := by rw [ht]; field_simp
      have : t ^ 2 * C - 2 * t * y ≤ 0 := by rw [hC]; nlinarith [hineq]
      have h3 : (t * (|C| + 1)) ^ 2 * C - 2 * (t * (|C| + 1)) * y * (|C| + 1) ≤ 0 := by
        have := mul_nonneg (le_of_lt (pow_pos hD 2)) (neg_nonneg.mpr this)
        nlinarith [this]
      rw [e1] at h3
      nlinarith [h3]
    have hCpos : 0 < C + 2 * (|C| + 1) := by
      have := neg_abs_le C
      linarith
    have hy2 : y ^ 2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos hcon hCpos]
    exact hy (by nlinarith [sq_nonneg y])
  -- nonnegative elements have nonnegative values
  have hpos : ∀ c : A, 0 ≤ c → 0 ≤ φ c := by
    intro c hc
    have hsa : IsSelfAdjoint c := IsSelfAdjoint.of_nonneg hc
    have hre := him c hsa
    set r : ℝ := ‖c‖ with hr
    have hcr : c ≤ algebraMap ℝ A r := hsa.le_algebraMap_norm_self
    have hnn : 0 ≤ algebraMap ℝ A r - c := sub_nonneg.mpr hcr
    have hle2 : algebraMap ℝ A r - c ≤ algebraMap ℝ A r := sub_le_self _ hc
    have hnorm : ‖algebraMap ℝ A r - c‖ ≤ r := by
      refine (CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle2).trans ?_
      rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one, Real.norm_eq_abs, hr]
      exact le_of_eq (abs_of_nonneg (norm_nonneg _))
    have hphi : φ (algebraMap ℝ A r - c) = (r : ℂ) - φ c := by
      rw [map_sub, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, h1]
      simp
    have hb := (hle _).trans hnorm
    rw [hphi] at hb
    have hx : φ c = ((φ c).re : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rw [hx] at hb
    have : ‖(r : ℂ) - ((φ c).re : ℂ)‖ = |r - (φ c).re| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [this] at hb
    have := (abs_le.mp hb).2
    rw [Complex.nonneg_iff]
    exact ⟨by linarith, by simp [hre]⟩
  intro a b hab
  have := hpos (b - a) (sub_nonneg.mpr hab)
  rw [map_sub] at this
  exact sub_nonneg.mp this
open scoped ComplexOrder in
/-- d13f23b's `PositiveLinearMap.norm_map_star_mul_sq_le`: Cauchy–Schwarz for a positive functional
(Kadison similarity, oaiq-075). -/
theorem _root_.PositiveLinearMap.norm_map_star_mul_sq_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (a b : A) :
    ‖ψ (star a * b)‖ ^ 2 ≤ ‖ψ (star a * a)‖ * ‖ψ (star b * b)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (ψ.toPreGNS a) (ψ.toPreGNS b)
  rw [PositiveLinearMap.preGNS_inner_def] at h
  have ha := ψ.preGNS_norm_sq (ψ.toPreGNS a)
  have hb := ψ.preGNS_norm_sq (ψ.toPreGNS b)
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS] at h ha hb
  have h2 := mul_self_le_mul_self (norm_nonneg _) h
  rw [← ha, ← hb]
  simpa [sq, mul_mul_mul_comm] using h2
/-- Mathlib d13f23b's `IsUnital`: a non-unital ring with a two-sided identity element (Kadison similarity,
oaiq-075). -/
class IsUnital (A : Type*) [NonUnitalRing A] : Prop where
  exists_one : ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a

/-- d13f23b's `IsUnital.toNormedRing`: a non-unital normed ring with an identity is a normed ring. -/
@[instance_reducible]
noncomputable def IsUnital.toNormedRing {A : Type*} [NonUnitalNormedRing A] [h : IsUnital A] :
    NormedRing A :=
  let e := h.exists_one.choose
  have he := h.exists_one.choose_spec
  letI : One A := ⟨e⟩
  letI : NatCast A := ⟨Nat.unaryCast⟩
  letI : IntCast A := ⟨Int.castDef⟩
  { ‹NonUnitalNormedRing A› with
    one_mul := fun a => (he a).1
    mul_one := fun a => (he a).2
    natCast_zero := rfl
    natCast_succ := fun n => rfl
    intCast_ofNat := fun n => rfl
    intCast_negSucc := fun n => rfl }
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `Complex.hasTemperateGrowth_exp_mul_I`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem hasTemperateGrowth_exp_mul_I : (fun x : ℝ => Complex.exp (x * Complex.I)).HasTemperateGrowth := by
  have hit : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)))
      = fun x : ℝ => Complex.I ^ n * Complex.exp (Complex.I * (x:ℂ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h1 : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)))
          (Complex.exp (Complex.I * (x:ℂ)) * Complex.I) x := by
        have := ((hasDerivAt_id x).ofReal_comp.const_mul Complex.I).cexp
        simpa using this
      have h2 := h1.const_mul (Complex.I ^ n)
      rw [h2.deriv]
      ring
  refine ⟨?_, fun n => ⟨0, 1, fun x => ?_⟩⟩
  · exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  · have h : (fun x : ℝ => Complex.exp (x * Complex.I)) = fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)) := by
      funext x; rw [mul_comm]
    rw [h, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit]
    simp [norm_pow, Complex.norm_exp]
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
open scoped ContDiff in
/-- Backport (Mathlib d13f23b), with Mathlib's own proof: the iterated derivatives up to order `m` of a
smooth compactly supported function are uniformly bounded (Falconer all dimensions, oaiq-088: 3 modules;
OAIHecke carried its own copy). -/
theorem _root_.HasCompactSupport.exists_bound_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  grw [hA i y, ← le_max_right]
  exact Finset.le_sup' A (by grind)
/-- Mathlib d13f23b's `Matrix.posSemidef_is_closed` (real matrices): positive semidefinite matrices are
closed (EinsteinFour JacobiCompressionLimit, oaiq-091). -/
open scoped Matrix in
theorem _root_.Matrix.posSemidef_is_closed {n : Type*} [Fintype n] :
    IsClosed {M : Matrix n n ℝ | M.PosSemidef} := by
  have h : {M : Matrix n n ℝ | M.PosSemidef} =
      {M : Matrix n n ℝ | M.IsHermitian} ∩
        ⋂ x : n → ℝ, {M : Matrix n n ℝ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp [Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [h]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · exact isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id
  · exact isClosed_le continuous_const (by fun_prop)
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod
alias List.Nodup.getElem?_inj := List.getElem?_inj
end OAICompat434

