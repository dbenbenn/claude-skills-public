import CarveDev.Base

/-! # CarveDev.InstBase: exports and instances across modules

* RationalHitting (2026-10-24): `export Coding (code)` was copied into a bundle that neither
  declares nor imports the class `Coding`: "unknown namespace `Coding`".
* RationalHitting: the instance `witnessCharZero` of a later module (InstLate here) reached the
  carved `list_hits` through a bundle and changed how `algebraMap ℚ` elaborated there.
* Problem340 (2026-10-24): sibling modules (InstA, InstB) each declare the same anonymous
  `local instance` of a Prop class; Lean gives both one name, the declaration graph keeps one, and
  the other module's instance never came back for the declarations that need it. -/

namespace CD.Ex

structure Word where
  val : Nat

class Coding (A : Type) where
  code : A → Nat

export Coding (code)

instance : Coding Nat := ⟨id⟩

def Word.len (w : Word) : Nat := w.val

theorem word_len (w : Word) : w.len = w.val := rfl

end CD.Ex

namespace CD.LI

class PropC (n : Nat) : Prop where
  out : n = n

structure Box where
  b : Nat

def Box.get (x : Box) : Nat := x.b

theorem box_get (x : Box) : x.get = x.b := rfl

end CD.LI
