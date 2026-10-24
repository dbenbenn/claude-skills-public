import CarveDev.InstBase

namespace CD.LI

/-- Solves `Inhabited Box` with InstBase's boxInhabitedA, before this module's own instance below:
a file showing that one here (from a bundle) is the one leak the carver cannot hide. -/
theorem late_default : (default : Box).b = 1 := rfl

/-- An instance a later module declares: the earlier `box_get` never saw it. -/
instance boxInhabited : Inhabited Box := ⟨⟨7⟩⟩

def defaultBox : Box := default

end CD.LI
