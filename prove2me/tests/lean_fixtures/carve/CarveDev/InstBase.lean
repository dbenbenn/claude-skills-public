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

/-- Asks instance search for a `PropC n`: a statement using it at `3` needs the local instance. -/
def needsPropC (n : Nat) [PropC n] : Nat := n

instance boxInhabitedA : Inhabited Box := ⟨⟨1⟩⟩

/-- Instance search solves an `Inhabited Box` here (with boxInhabitedA): InstLate's later
`boxInhabited`, visible in a carved file, would win instead, and this `rfl` would fail. -/
theorem box_default : (default : Box).b = 1 := rfl

/-- A binder supplies the `Inhabited Box`: a local instance comes before every global one, so
no instance a carved file newly shows can take part. -/
theorem box_default_local [Inhabited Box] : (default : Box).get = (default : Box).b := rfl

/-- CoulombAtom (oaiq-071): instance search solves `Inhabited (Option Nat)` here, and InstLate's
`natOptInhabited` on the abbrev `NatOpt` (= `Option Nat`), visible in a carved file through a
bundle, would win; its type mentions no project declaration this one uses (only `NatOpt`). -/
theorem opt_default : (default : Option Nat) = none := rfl

end CD.LI
