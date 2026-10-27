import CarveDev.Mid
import CarveDev.Alt
import CarveDev.Fields
import CarveDev.InstA
import CarveDev.InstB
import CarveDev.InstLate
import CarveDev.Coer
import CarveDev.InstColB

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

theorem uses_sized (B : Space) : (sizedZero B).val = 0 := rfl

theorem uses_scoped : viaScoped 1 = 2 := rfl

@[simp] theorem simpA : 1 + 0 = 1 := rfl

attribute [-simp] simpA

end CD

namespace CD.Aux

def laterConst : Nat := 7

end CD.Aux
