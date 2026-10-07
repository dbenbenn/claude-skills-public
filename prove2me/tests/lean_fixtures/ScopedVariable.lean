import Mathlib

namespace A
def CA : Type := Nat
def keepA : Nat := 0
end A

namespace B
def CA : Type := Nat
def useB : CA := (0 : Nat)
end B

namespace C
open A
variable (x : CA) (n : Nat)
theorem unusedC (y : CA) : y = y := rfl
end C

namespace E
def named : Nat := 0
variable (k : Nat) (hk : k = k)
local notation "GG" => named + k
end E

theorem solution : B.useB = B.useB ∧ A.keepA = 0 := ⟨rfl, rfl⟩
