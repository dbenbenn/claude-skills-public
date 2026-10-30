import CarveDev.LocalCtx

/-! # CarveDev.LocalFor: a module's own local instance, answered for a foreign one

Finitistic (q128-finitistic-retry, 2026-10-30): `IntegerIterateAmplitude` declared
`local instance : HasDerivedCategory (ModuleCat D) := HasDerivedCategory.standard _`, and
`resolvedModelIso` needed it, but its record named only the defeq local instance of another
module (`DerivedBar.instHasDerivedCategoryModuleCat_solutions`, reached by unification through an
imported abbrev); the bundle dropped the module's own one ("failed to synthesize
HasDerivedCategory"). Here `dqPair` of LocalCtx is the foreign one, on a library type as there. -/

namespace CD.LF
open CD.LC

section
local instance : Dq (Nat × Bool) := ⟨1⟩

theorem dq_for : Dq.d (Nat × Bool) = 1 := rfl
end

end CD.LF
