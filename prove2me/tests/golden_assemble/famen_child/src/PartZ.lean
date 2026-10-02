import Solutions.FAmenChild.Blueprint

/-! Assembly of the child from the Blueprint lemmas. -/

open scoped ENNReal Pointwise
open CannonFloydParry

namespace FAmenChild.PartZ

/-- The linear part: `g · φ = mapDomain (g • ·) φ`. -/
noncomputable def lin (g : F) (φ : UI →₀ ℤ) : UI →₀ ℤ := Finsupp.mapDomain (fun x => g • x) φ

theorem lin_one (φ : UI →₀ ℤ) : lin 1 φ = φ := by
  simp only [lin, one_smul]
  exact Finsupp.mapDomain_id

theorem lin_mul (g h : F) (φ : UI →₀ ℤ) : lin (g * h) φ = lin g (lin h φ) := by
  simp only [lin]
  rw [← Finsupp.mapDomain_comp]
  congr 1

theorem lin_add (g : F) (φ ψ : UI →₀ ℤ) : lin g (φ + ψ) = lin g φ + lin g ψ :=
  Finsupp.mapDomain_add

theorem cocycle_one : cocycle (1 : F) = 0 := by
  have h := cocycle_mul (1 : F) 1
  have h2 : Finsupp.mapDomain (fun x => (1 : F) • x) (cocycle 1) = cocycle 1 := lin_one _
  rw [mul_one, h2] at h
  have := congrArg (fun φ => φ - cocycle (1 : F)) h
  simpa using this.symm

/-- The affine action `g ⋆ φ = cocycle g + g · φ`. -/
@[instance_reducible] noncomputable def affAction : MulAction F (UI →₀ ℤ) where
  smul g φ := cocycle g + lin g φ
  one_smul φ := by
    show cocycle 1 + lin 1 φ = φ
    rw [cocycle_one, lin_one, zero_add]
  mul_smul g h φ := by
    show cocycle (g * h) + lin (g * h) φ = cocycle g + lin g (cocycle h + lin h φ)
    rw [cocycle_mul, lin_mul, lin_add]
    simp only [lin]
    abel

theorem isAmenable_F_of_isExtensivelyAmenableOn
    (h : ThompsonAmenability.IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI
      {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x}) :
    Garrido.IsAmenable CannonFloydParry.F := by
  obtain ⟨μ, hμ, h1, hlin, htr⟩ := exists_affine_mean _ h
  let _ := affAction
  have hsmul : ∀ (g : F) (φ : UI →₀ ℤ), g • φ = cocycle g + lin g φ := fun _ _ => rfl
  refine isAmenable_of_free (G := F) (Y := UI →₀ ℤ) ?_ μ hμ h1 ?_
  · intro g φ hg
    rw [hsmul] at hg
    exact cocycle_free g φ hg
  · intro g S
    have hS : g • S = (cocycle g + ·) '' ((Finsupp.mapDomain (fun x => g • x)) '' S) := by
      ext φ
      simp only [Set.mem_smul_set, Set.mem_image, hsmul, lin]
      constructor
      · rintro ⟨ψ, hψ, rfl⟩; exact ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩; exact ⟨ψ, hψ, rfl⟩
    rw [hS, htr (cocycle g) (cocycle_support g)]
    exact hlin g S

end FAmenChild.PartZ
