/-! # CarveDev.ShadowA: a project declaration named like a library one

* oaiq-096 (CubicMoment, 2026-10-29): `lemma norm_nonneg (z : Eisenstein)` in namespace
  `OAI.CubicFirstMoment` shadowed Mathlib's `norm_nonneg` for every other module of a carved piece
  (ShadowB here, which never imports it): `norm_nonneg _` read the project lemma, "Type mismatch". -/

namespace CD.Sh

theorem Nat.le_refl (n : Nat) : n ≤ n + 0 := _root_.Nat.le_refl n

end CD.Sh
