import CarveDev.InstBase

namespace CD.LI

local instance : PropC 3 := ⟨rfl⟩

theorem uses_propc_a : PropC 3 := inferInstance

/-- The statement itself needs the local `Prop` instance (instance search, no name in the text):
a statement stub keeps it (Erdős 3 v2: `local instance forecastModulusNeZero`, which makes
`ZMod (∏ …)` finite in a statement). -/
theorem uses_propc_sig : needsPropC 3 = 3 := rfl

end CD.LI
