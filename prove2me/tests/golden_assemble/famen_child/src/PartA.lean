import Solutions.FAmenChild.Blueprint

/-!
# Part A: a free action with an invariant finitely additive probability

Choose a representative `rep y` of each orbit; freeness gives a unique `coord y : G` with
`coord y • rep y = y`, and `coord (h • y) = h * coord y`.  Pulling `m` back along `coord`
gives a left-invariant finitely additive probability on `G`.
-/

open scoped ENNReal Pointwise

namespace FAmenChild.PartA

/-- The chosen representative of the orbit of `y`. -/
noncomputable def rep (G : Type*) {Y : Type*} [Group G] [MulAction G Y] (y : Y) : Y :=
  (Quotient.mk (MulAction.orbitRel G Y) y).out

lemma exists_smul_rep {G Y : Type*} [Group G] [MulAction G Y] (y : Y) :
    ∃ g : G, g • rep G y = y := by
  have h : rep G y ∈ MulAction.orbit G y := by
    have := Quotient.mk_out (s := MulAction.orbitRel G Y) y
    exact (MulAction.orbitRel_apply).1 this
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

lemma rep_smul {G Y : Type*} [Group G] [MulAction G Y] (h : G) (y : Y) :
    rep G (h • y) = rep G y := by
  unfold rep
  congr 1
  exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit y h))

/-- The coordinate of `y`: the group element carrying the representative to `y`. -/
noncomputable def coord (G : Type*) {Y : Type*} [Group G] [MulAction G Y] (y : Y) : G :=
  (exists_smul_rep (G := G) y).choose

lemma coord_smul_rep {G Y : Type*} [Group G] [MulAction G Y] (y : Y) :
    coord G y • rep G y = y :=
  (exists_smul_rep (G := G) y).choose_spec

lemma coord_smul {G Y : Type*} [Group G] [MulAction G Y]
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) (h : G) (y : Y) :
    coord G (h • y) = h * coord G y := by
  have e1 := coord_smul_rep (G := G) (h • y)
  rw [rep_smul] at e1
  have e2 : (h * coord G y) • rep G y = h • y := by rw [mul_smul, coord_smul_rep]
  have : ((h * coord G y)⁻¹ * coord G (h • y)) • rep G y = rep G y := by
    rw [mul_smul, e1, ← e2, inv_smul_smul]
  have h1 := hfree _ _ this
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem isAmenable_of_free {G Y : Type*} [Group G] [MulAction G Y]
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1)
    (m : Set Y → ℝ≥0∞) (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (hinv : ∀ (g : G) (S : Set Y), m (g • S) = m S) : Garrido.IsAmenable G := by
  refine ⟨fun S => m ((coord G : Y → G) ⁻¹' S), ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa using hm.1
  · intro s t hst
    simpa [Set.preimage_union] using hm.2 _ _ (hst.preimage _)
  · simpa using h1
  · intro g S
    have : (coord G : Y → G) ⁻¹' (g • S) = g • ((coord G : Y → G) ⁻¹' S) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
        coord_smul hfree]
    simp only
    rw [this, hinv]

end FAmenChild.PartA
