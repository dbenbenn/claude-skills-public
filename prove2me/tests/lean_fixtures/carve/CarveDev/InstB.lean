import CarveDev.InstBase

namespace CD.LI

local instance : PropC 3 := ⟨rfl⟩

theorem uses_propc_b : PropC 3 := inferInstance

/-- As `uses_propc_sig`, here the module whose anonymous instance has no node of its own. -/
theorem uses_propc_sig_b : needsPropC 3 = 3 := rfl

end CD.LI
