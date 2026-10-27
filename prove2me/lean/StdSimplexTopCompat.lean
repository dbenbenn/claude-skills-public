import Mathlib
import @MOD@.StdSimplexCompat

open CategoryTheory Simplicial

noncomputable section

/-! ## Part 3: `SimplexCategory.toTopHomeoD`, `toTopHomeo` with the structure `Convexity.StdSimplex` -/

namespace OAI.SStd

/-- The subtype `stdSimplex ℝ X` and the structure `Convexity.StdSimplex ℝ X` are homeomorphic. -/
noncomputable def homeoStdSimplex (X : Type*) [Fintype X] :
    SStd ℝ X ≃ₜ Convexity.StdSimplex ℝ X where
  toEquiv := equivStdSimplex
  continuous_toFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ X).continuous_iff.mpr
    exact continuous_pi fun k => (continuous_apply k).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun k => ?_
    exact Convexity.StdSimplex.continuous_weights_apply ℝ k

end OAI.SStd

/-- `d13f23b`'s `SimplexCategory.toTopHomeo`: the realization of `Δ[n]` is homeomorphic to
`Convexity.StdSimplex ℝ (Fin (n.len + 1))`. -/
noncomputable def SimplexCategory.toTopHomeoD (n : SimplexCategory) :
    ↑(SSet.toTop.obj (SSet.stdSimplex.obj n)) ≃ₜ Convexity.StdSimplex ℝ (Fin (n.len + 1)) :=
  n.toTopHomeo.trans (OAI.SStd.homeoStdSimplex _)

theorem SimplexCategory.toTopHomeoD_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : ↑(SSet.toTop.obj (SSet.stdSimplex.obj n))) :
    m.toTopHomeoD ((ConcreteCategory.hom (SSet.toTop.map (SSet.stdSimplex.map f))) x) =
      Convexity.StdSimplex.map (⇑(ConcreteCategory.hom f)) (n.toTopHomeoD x) := by
  apply Convexity.StdSimplex.ext
  ext k
  simp only [SimplexCategory.toTopHomeoD, Homeomorph.trans_apply,
    SimplexCategory.toTopHomeo_naturality_apply]
  simp [OAI.SStd.homeoStdSimplex, OAI.SStd.equivStdSimplex, OAI.SStd.toStdSimplex,
    OAI.SStd.weights, Convexity.StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Finsupp.single_apply]
  change (FunOnFinite.linearMap ℝ ℝ _ (n.toTopHomeo x).1) k = _
  rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
