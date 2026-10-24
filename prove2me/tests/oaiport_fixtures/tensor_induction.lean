open scoped TensorProduct

namespace OAI.TensorFix

open TensorProduct

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- A motive `simp` does not see through: no `map_zero`-style lemma proves `Good 0`. -/
def Good (_ : M ⊗[R] N) : Prop := True

theorem good_of (h : ∀ x y, Good (x ⊗ₜ[R] y : M ⊗[R] N)) (z : M ⊗[R] N) : Good z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add a b ha hb => trivial

-- the `induction` line indented 3, its alternatives 2 (Boone–Higman Corners)
theorem ext_of (f g : M ⊗[R] N →ₗ[R] P) (h : ∀ x y, f (x ⊗ₜ y) = g (x ⊗ₜ y)) (z : M ⊗[R] N) :
    f z = g z := by
   induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul x y => exact h x y

-- nested, inside an alternative (ComparatorModel SpatialTensor)
theorem ext₂_of (f g : M ⊗[R] N →ₗ[R] M ⊗[R] N →ₗ[R] P)
    (h : ∀ x y x' y', f (x ⊗ₜ y) (x' ⊗ₜ y') = g (x ⊗ₜ y) (x' ⊗ₜ y')) (z w : M ⊗[R] N) :
    f z w = g z w := by
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb]
    | tmul x y =>
      induction w using TensorProduct.inductionOn with
      | add a b ha hb => rw [map_add, map_add, ha, hb]
      | tmul x' y' => exact h x y x' y'

-- no `with`: one bullet per remaining goal
theorem good_of' (h : ∀ x y, Good (x ⊗ₜ[R] y : M ⊗[R] N)) (z : M ⊗[R] N) : Good z := by
  induction z using TensorProduct.inductionOn
  · exact h _ _
  · trivial

-- term mode
theorem good_of'' (h : ∀ x y, Good (x ⊗ₜ[R] y : M ⊗[R] N)) (z : M ⊗[R] N) : Good z :=
  TensorProduct.inductionOn z h fun _ _ _ _ => trivial

end OAI.TensorFix
