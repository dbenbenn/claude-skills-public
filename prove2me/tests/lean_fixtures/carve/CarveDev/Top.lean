import CarveDev.Mid
import CarveDev.Alt

universe u

namespace CD

theorem top_pick {α : Sort u} (a : α) : pick (pick a) = a := by rw [pick_eq, pick_eq]

open Aux

private theorem helper : 1 = 1 := rfl

theorem main (A : Space) (n : Nat) : A.size + double (n + 1) = double n + 2 + List.headOr [] := by
  have := helper
  have : quad 0 = 0 := rfl
  have := size_via_coord A
  rw [size_zero, double_succ, List.headOr_nil]; omega

open _root_.CD.Aux in
theorem top_aux : auxOnly = 1 := aux_eq

theorem uses_sorry : usesSorried = 0 := rfl

end CD
