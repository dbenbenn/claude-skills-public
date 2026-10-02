import Mathlib

namespace A

/-- doc -/
theorem foo' (n : ℕ) : n = n := rfl

@[simp] theorem s1 (n : ℕ) : n + 0 = n := Nat.add_zero n

@[simp]
theorem s2 (n : ℕ) : 0 + n = n := Nat.zero_add n

open Nat in
theorem viaIn : (2 : ℕ) = 2 := foo' 2

private theorem hidden : True := trivial

theorem usesHidden : True := hidden

end A

/-!
theorem for balls: a module docstring line beginning with "theorem"
-/

section B
variable {X : Type} (x : X)

theorem inSec1 : x = x := rfl

theorem inSec2 : x = x := inSec1 x
end B

def f (n : ℕ) : ℕ := match n with
  | 0 => 1
  | k + 1 => k

theorem f_zero : f 0 = 1 := rfl

structure P where
  a : ℕ

instance : Inhabited P := ⟨⟨0⟩⟩

theorem solution : A.foo' 3 = A.foo' 3 ∧ f 0 = 1 := ⟨rfl, f_zero⟩
