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

-- an rfl lemma used only through `simp only`: simp rewrites by dsimp, so the proof term never
-- mentions it (Moore's bits_001, 2026-10-02)
theorem f_one : f 1 = 0 := rfl

theorem viaSimp : f 1 + 1 = 1 := by simp only [f_one]

-- Mathlib's `lemma` is its own command kind, not core's `declaration`
lemma viaLemma : f 0 = 1 := f_zero

open A in
lemma unusedLemma : foo' 1 = foo' 1 := rfl

def g1 : ℕ := 1
def g2 : ℕ := 2

/-! ### Structures -/

structure P where
  a : ℕ

instance : Inhabited P := ⟨⟨0⟩⟩

theorem solution : A.foo' 3 = A.foo' 3 ∧ f 0 = 1 := ⟨rfl, f_zero⟩
