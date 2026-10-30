import CarveDev.SimpLate
import CarveDev.SimpUse

namespace CD.Sp

theorem simpTop (n : Nat) : h (n + 0) = n ∧ h n = n := ⟨use n, late n⟩

end CD.Sp
