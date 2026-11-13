/-! # CarveDev.InstPriv: `private noncomputable` instances

Duke MainUnconditional (q359, 2026-11-13). The carver's instance patterns read the modifiers in the
order `noncomputable private`; Lean writes `private noncomputable`, so these commands were not
recognised as instances at all:
* an anonymous `private noncomputable instance : ∀ E, SMul …` was emitted, deprivatized, still
  anonymous; Lean named it differently in the bundle, and a later section's `attribute [-instance]`
  under the port's name failed ("Unknown constant"). Here the anonymous `Tag (Fld n)` instance.
* four `private noncomputable local instance`s (a `UniformSpace` at priority 50, …) of a module whose
  first part went into one bundle: the bundle holding the rest did not put them back in force
  ("failed to synthesize TopologicalSpace"). Here `fldUnif` (priority 50) and `fldInh`. -/

namespace CD.PI

structure Fld (n : Nat) where
  x : Nat

class Tag (α : Type) where
  t : Nat

class Unif (α : Type) where
  u : Nat

private noncomputable instance : ∀ n : Nat, Tag (Fld n) := fun _ => ⟨7⟩

theorem tag_fld (n : Nat) : Tag.t (Fld n) = 7 := rfl

section

private noncomputable local instance (priority := 50)
    fldUnif (n : Nat) : Unif (Fld n) := ⟨1⟩

private noncomputable local instance
    fldInh (n : Nat) : Inhabited (Fld n) := ⟨⟨3⟩⟩

noncomputable def fldDefault (n : Nat) : Fld n := default

theorem fld_later (n : Nat) : (default : Fld n).x = 3 ∧ Unif.u (Fld n) = 1 := ⟨rfl, rfl⟩

end

end CD.PI
