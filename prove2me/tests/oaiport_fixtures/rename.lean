namespace OAI

namespace Fold

structure Cuts where
  main : Nat
  side : Nat

inductive State where
  | main
  | aux (n : Nat)

def start : Cuts where
  main := 1
  side := 2

def pick (j : Nat) : Cuts := { main := j, side := j }

def stateName : State → Nat
  | .main => 0
  | State.aux n => n

def withBinders : Cuts where
  main := 3
  side := 4

theorem helper : True := trivial

theorem main : True := helper

theorem uses_main : True := main

theorem uses_qualified : True := Fold.main

theorem uses_full : True := OAI.Fold.main

theorem field_access (c : Cuts) : c.main = c.main := rfl

theorem mathlib_name : Nat.succ 0 = 1 := rfl

end Fold

namespace Elsewhere
theorem main : True := trivial
theorem uses_other : True := main
end Elsewhere

end OAI
