import CarveDev.ExpOnly

/-! # CarveDev.ExpUse: declarations that name ExpOnly's aliases -/

namespace CD.EX

theorem uses_alias (n : Nat) : Alias.val n = n + 2 := Alias.val_eq n

theorem uses_alias_top : Alias.val 0 = 2 := uses_alias 0

end CD.EX
