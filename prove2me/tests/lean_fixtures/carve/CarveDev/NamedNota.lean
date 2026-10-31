/-! # CarveDev.NamedNota: named local notations in a piece and in its statement

q142 (JointDickman, `Erdos970_PNT5_Strong`): `local notation (name := mellintransform2) "𝓜" =>
MellinTransform` is a private declaration `Erdos970.mellintransform2`. The piece and the statement
stub it proves both carried the line, and the server-shape check (solution, then statement, in one
file) failed "private declaration … has already been declared". An anonymous local notation
repeats without trouble. -/

namespace CD.NN

def twice (n : Nat) : Nat := 2 * n

local notation (name := twiceNota) "𝓣" => twice
local infixl:65 (name := plusNota) " ⊞ " => Nat.add

theorem tw_zero : 𝓣 0 = 0 := rfl

theorem tw_top : 𝓣 0 ⊞ 𝓣 0 = 0 := by rw [tw_zero]

end CD.NN
