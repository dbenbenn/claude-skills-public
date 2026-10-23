import CarveDev.InstBase

namespace CD.LI

/-- An instance a later module declares: the earlier `box_get` never saw it. -/
instance boxInhabited : Inhabited Box := ⟨⟨7⟩⟩

def defaultBox : Box := default

end CD.LI
