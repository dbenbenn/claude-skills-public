import CarveDev.Base

universe u

namespace CD

theorem pick_eq {α : Sort u} (a : α) : pick a = a := rfl

/-- A coordinate of a space. -/
def Space.coord (_A : Space) : Nat := 0

theorem Space.coord_eq (A : Space) : A.coord = 0 := rfl

/-- `A.coord_eq` is named only in the source, through the local `A`'s dot notation, and `dsimp`
leaves no trace of it in the term (Erdős 3 B024, "Unknown identifier `coord`"). -/
theorem size_via_coord (A : Space) : A.coord + A.size = 0 := by
  dsimp only [A.coord_eq]
  simp

/-- Four times, a definition of this module (so Mid has bundle material of its own). -/
def quad (n : Nat) : Nat := double (double n)

open List

local notation "DE" => double_eq

/-- Double zero, through the notation. -/
theorem double_zero : double 0 = 0 := DE 0

private theorem helper : True := trivial

variable (A : Space)
  (n : Nat)
  (hx : Aux.auxOnly = 1)

include hx

theorem uses_hx : Aux.auxOnly = 1 := hx

omit
  hx in
theorem size_zero : A.size = 0 := by simp

omit hx in
theorem double_succ : double (n + 1) = double n + 2 := by
  have := helper
  simp only [double_eq]; omega

#check double_succ

end CD
