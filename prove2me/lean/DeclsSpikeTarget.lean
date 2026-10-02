import Mathlib

namespace Foo

/-- doc -/
theorem bar' (n : ℕ) : n + 0 = n := by simp

open Nat in
theorem baz : (2 : ℕ) + 0 = 2 := bar' 2

end Foo

theorem solution : (3 : ℕ) + 0 = 3 := Foo.bar' 3
