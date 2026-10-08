import CarveDev.Base

namespace CD.List

/-- The head of a list of naturals, or zero. -/
def headOr (l : _root_.List Nat) : Nat := l.headD 0

theorem headOr_nil : headOr [] = 0 := rfl

end CD.List

namespace CD.Mac

macro "twice! " t:term : term => `($t + $t)

def useMac : Nat := twice! 1

end CD.Mac
