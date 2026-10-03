import Mathlib

structure Data (X : Type) where
  Q : Type
  q : Q

section S

variable {X : Type} [Inhabited X] (d : Data X)

theorem keepX (x : X) : x = x := rfl

theorem usesD : d.Q = d.Q := rfl

end S

section T

variable {Q : Type} (m : Q → Prop)

theorem keepQ (q : Q) (h : m q) : m q := h

end T

theorem solution : True := by
  have := keepQ (Q := ℕ) (fun _ => True) 0 trivial
  trivial
