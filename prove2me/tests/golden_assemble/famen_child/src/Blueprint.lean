import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability

/-!
# Extensive amenability of `F ↷ D` implies amenability of `F`

`D` is the set of dyadic rationals in `(0,1)`. Chornyi (arXiv:1907.01440, p. 7, proof of
Corollary 3) defines `c(g)(x) = g'₊(x) / g'₋(x)`, valued in the powers of `2`, observes that
`g ↦ (c(g), g)` is a cocycle with trivial kernel, and applies the criterion of
Juschenko–Matte Bon–Monod–de la Salle (arXiv:1503.04977, Corollary 1.4 and Remark 1.5).
This file proves the case of that criterion the argument needs, with the exponents of `2`
(the group `ℤ`) as lamps:

* (C) The slope-jump cocycle `c : F → (UI →₀ ℤ)` (supported in `D`) makes the affine action
  `g ⋆ φ = c g + g · φ` free: no `g ≠ 1` fixes any `φ` (`φ = 0` is the trivial kernel).
* (B) Extensive amenability of `F ↷ D` gives a finitely additive probability on `Set (UI →₀ ℤ)`
  invariant under the linear action of `F` and under translations supported in `D`; hence
  invariant under `⋆`.
* (A) A free action with an invariant finitely additive probability makes the group amenable.
-/

open scoped ENNReal Pointwise

namespace FAmenChild

/-! ## Part A -/

theorem isAmenable_of_free {G Y : Type*} [Group G] [MulAction G Y]
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1)
    (m : Set Y → ℝ≥0∞) (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (hinv : ∀ (g : G) (S : Set Y), m (g • S) = m S) : Garrido.IsAmenable G := by
  sorry

/-! ## Part B1: integrating `[0,1]`-valued functions against a finitely additive probability -/

/-- `∑_{k < 2^n} 2^{-n} m {f ≥ (k+1)/2^n}`: the integral of `⌊2^n f⌋ / 2^n`. -/
noncomputable def layerSum {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n

/-- The integral: the supremum of the layer sums. -/
noncomputable def integ {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) : ℝ := ⨆ n, layerSum m f n

section B1
variable {α : Type*} {m : Set α → ℝ≥0∞}

theorem integ_indicator (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : integ m (S.indicator 1) = (m S).toReal := by
  sorry

theorem integ_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (hfg : ∀ a, f a + g a ≤ 1) :
    integ m (f + g) = integ m f + integ m g := by
  sorry

theorem integ_congr (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (h : m {a | f a ≠ g a} = 0) : integ m f = integ m g := by
  sorry

theorem integ_comp_equiv (τ : α ≃ α) (hτ : ∀ S : Set α, m (τ '' S) = m S) (f : α → ℝ) :
    integ m (f ∘ τ) = integ m f := by
  sorry

theorem integ_nonneg_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : 0 ≤ integ m f ∧ integ m f ≤ 1 := by
  sorry

end B1

/-! ## Part B2: symmetric translation-invariant means on finitely supported `ℤ`-functions -/

theorem exists_symMean (n : ℕ) : ∃ μ : Set (Fin n → ℤ) → ℝ≥0∞,
    Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1 ∧
    (∀ (v : Fin n → ℤ) (S : Set (Fin n → ℤ)), μ ((v + ·) '' S) = μ S) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (S : Set (Fin n → ℤ)), μ ((fun w => w ∘ σ) '' S) = μ S) := by
  sorry

noncomputable def symMean (n : ℕ) : Set (Fin n → ℤ) → ℝ≥0∞ := (exists_symMean n).choose

/-- The finitely supported function on `X` that is `w` on `A` (through `A.equivFin`) and `0`
off `A`. -/
noncomputable def extendFin {X : Type*} (A : Finset X) (w : Fin A.card → ℤ) : X →₀ ℤ :=
  Finsupp.onFinset A (fun x => open Classical in if h : x ∈ A then w (A.equivFin ⟨x, h⟩) else 0)
    (by intro x hx; by_contra h; simp [h] at hx)

/-- The mean on `X →₀ ℤ` carried by the finite set `A`. -/
noncomputable def meanOn {X : Type*} (A : Finset X) (S : Set (X →₀ ℤ)) : ℝ≥0∞ :=
  symMean A.card {w | extendFin A w ∈ S}

section B2
variable {X : Type*}

theorem meanOn_isFinitelyAdditiveMeasure (A : Finset X) :
    Garrido.IsFinitelyAdditiveMeasure (meanOn A) ∧ meanOn A Set.univ = 1 := by
  sorry

theorem meanOn_add (A : Finset X) (w : X →₀ ℤ) (hw : (↑w.support : Set X) ⊆ ↑A)
    (S : Set (X →₀ ℤ)) : meanOn A ((w + ·) '' S) = meanOn A S := by
  sorry

theorem meanOn_perm (σ : Equiv.Perm X) (A : Finset X) (S : Set (X →₀ ℤ)) :
    meanOn (A.map σ.toEmbedding) ((Finsupp.mapDomain σ) '' S) = meanOn A S := by
  sorry

end B2

/-! ## Part B3: the mean on `X →₀ ℤ` from extensive amenability -/

theorem exists_affine_mean {G X : Type*} [Group G] [MulAction G X] (Y : Set X)
    (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) :
    ∃ μ : Set (X →₀ ℤ) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1 ∧
      (∀ (g : G) (S : Set (X →₀ ℤ)), μ ((Finsupp.mapDomain (fun x => g • x)) '' S) = μ S) ∧
      (∀ w : X →₀ ℤ, (↑w.support : Set X) ⊆ Y → ∀ S, μ ((w + ·) '' S) = μ S) := by
  sorry

/-! ## Part C: the slope-jump cocycle of `F` and freeness of its affine action -/

open CannonFloydParry

/-- The dyadic rationals of `(0,1)`. -/
def D : Set UI := {x | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ IsDyadic x}

/-- The exponent `n` of the slope `2^n` of `f` just to the right of `x` (`0` if there is none). -/
noncomputable def rexp (f : UI ≃o UI) (x : UI) : ℤ :=
  open Classical in
  if h : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ n * z + c then h.choose else 0

/-- The exponent of the slope of `f` just to the left of `x` (`0` if there is none). -/
noncomputable def lexp (f : UI ≃o UI) (x : UI) : ℤ :=
  open Classical in
  if h : ∃ (n : ℤ) (c δ : ℝ), 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ n * z + c then h.choose else 0

/-- The jump of the slope exponent at a point of `D` (`0` elsewhere). -/
noncomputable def jumpFun (f : UI ≃o UI) (x : UI) : ℤ :=
  open Classical in if x ∈ D then rexp f x - lexp f x else 0

theorem rexp_spec {f : UI ≃o UI} (hf : f ∈ F) {x : UI} (hx : (x : ℝ) < 1) :
    ∃ c δ : ℝ, 0 < δ ∧ ∀ z : UI, (x : ℝ) ≤ z → (z : ℝ) ≤ x + δ →
      (f z : ℝ) = 2 ^ rexp f x * z + c := by
  sorry

theorem lexp_spec {f : UI ≃o UI} (hf : f ∈ F) {x : UI} (hx : 0 < (x : ℝ)) :
    ∃ c δ : ℝ, 0 < δ ∧ ∀ z : UI, (x : ℝ) - δ ≤ z → (z : ℝ) ≤ x →
      (f z : ℝ) = 2 ^ lexp f x * z + c := by
  sorry

theorem jumpFun_finite {f : UI ≃o UI} (hf : f ∈ F) : (Function.support (jumpFun f)).Finite := by
  sorry

noncomputable def jump (g : F) : UI →₀ ℤ :=
  Finsupp.ofSupportFinite (jumpFun (g : UI ≃o UI)) (jumpFun_finite g.2)

/-- The cocycle `c g = g · jump g`, i.e. `c g x = jump g (g⁻¹ x)`. -/
noncomputable def cocycle (g : F) : UI →₀ ℤ := Finsupp.mapDomain (fun x => g • x) (jump g)

theorem cocycle_support (g : F) : (↑(cocycle g).support : Set UI) ⊆ D := by
  sorry

theorem cocycle_mul (g h : F) :
    cocycle (g * h) = cocycle g + Finsupp.mapDomain (fun x => g • x) (cocycle h) := by
  sorry

theorem cocycle_free (g : F) (φ : UI →₀ ℤ)
    (h : cocycle g + Finsupp.mapDomain (fun x => g • x) φ = φ) : g = 1 := by
  sorry

/-! ## Assembly -/

theorem isAmenable_F_of_isExtensivelyAmenableOn
    (h : ThompsonAmenability.IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI
      {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x}) :
    Garrido.IsAmenable CannonFloydParry.F := by
  sorry

end FAmenChild
