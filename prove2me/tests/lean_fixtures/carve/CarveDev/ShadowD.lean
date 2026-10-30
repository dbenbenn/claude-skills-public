/-! # CarveDev.ShadowD: `some` and `none` in a dotted declaration, where ShadowC's `Pk.some` would capture them -/

namespace CD.Sh

def Pk.fin (q : Option Nat) : Nat :=
  match q with
  | none => 0
  | some n => n

def Pk.mk : Option Nat := some 3

theorem Pk.fin_le (q : Option Nat) : Pk.fin q ≤ Pk.fin q := by
  cases q with
  | none => exact Nat.le_refl _
  | some n => exact Nat.le_refl _

end CD.Sh
