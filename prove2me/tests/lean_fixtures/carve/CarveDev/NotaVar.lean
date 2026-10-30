/-! # CarveDev.NotaVar: a local notation written with a section variable named like a theorem

oaiq-081 (SubexponentialSAT): `local notation "seeded" => … run.output` with `run` a section
variable, in a module where the opened namespace also has a theorem `run`. LeanInfo resolves a
notation's body without the section's variables, so it recorded the theorem: the stub dropped the
notation ("needs a gone declaration"), and with the theorem `run` a target, its `run_oai` rename
replaced the field (`run.run_oai`). Also `export` in a namespace block holding no declaration
(`namespace PA / export PolynomialAlgorithm (denote) / end PA`): the block went whole, and the
piece's `PA.denote` was unknown. -/

namespace CD.NV

theorem run : 1 = 1 := rfl

structure R where
  output : Nat
  seed : Nat

section S

variable (run : R)

local notation "seeded" => run.output + run.seed
local notation "both" => seeded + 1

theorem uses : both = run.output + run.seed + 1 := rfl

end S

namespace PolyAlg

def denote (n : Nat) : Nat := n + 1

end PolyAlg

namespace PA
export PolyAlg (denote)
end PA

theorem denote_zero : PA.denote 0 = 1 := rfl

theorem both_run : 1 = 1 ∧ PA.denote 0 = 1 := ⟨run, denote_zero⟩

end CD.NV
