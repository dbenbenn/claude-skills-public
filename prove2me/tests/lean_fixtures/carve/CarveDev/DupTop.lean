import CarveDev.DupUseZ
import CarveDev.DupUseA
import CarveDev.DupUseA2

/-! DupUseZ is imported first, so the environment's `CD.Dup.bound` is DupZ's (`const2ModIdx`
keeps the first module), while the carver keeps DupA's (more importers) and renames DupZ's. -/

namespace CD.Dup

theorem dupMain (n : Nat) : n ≤ n + 1 ∧ n ≤ n + 1 + 0 ∧ n + 1 ≤ n + 1 + 1 :=
  ⟨useA n, useA2 n, useZ' n⟩

end CD.Dup
