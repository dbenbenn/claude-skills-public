/-! # CarveDev.ShadowC: a project declaration in a namespace that a dotted declaration name opens

* q135 (VertexCover, 2026-10-31): `noncomputable def Poly.some` (Machines/Option) and
  `noncomputable def Poly.finite` (Machines/FiniteMemory, which never imports it) shared bundle
  OAIQ028V004; in `Poly.finite` the namespace `Poly` is open, so `| some s =>` read `Poly.some`
  ("Invalid pattern"). -/

namespace CD.Sh

def Pk.some (n : Nat) : Nat := n + 1

end CD.Sh
