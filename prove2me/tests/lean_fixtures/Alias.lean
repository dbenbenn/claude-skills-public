import Mathlib

namespace Al.P

theorem used : True := trivial

theorem unused : True := trivial

end Al.P

namespace Al

alias used := Al.P.used

alias unused := Al.P.unused

end Al

local notation "TT" => True

theorem solution : TT := Al.used
