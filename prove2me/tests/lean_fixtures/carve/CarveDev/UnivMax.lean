/-! # CarveDev.UnivMax: a statement whose universes occur only under `max`

oaiq-124 (KL invariance): `boundary_edge_image_le` bound `{σ : Type (max us v)}` (`us` nowhere
bare); its piece measured ok locally and got WA "stuck at solving universe constraint
`max ?u.5 ?u.11 =?= max ?u.10 ?u.11`". The carver does not make such a theorem a statement of its
own choosing (it stays inside its importers' pieces, as `fold` would put it). -/

universe u v

namespace CD.UM

theorem maxOnly {σ : Type (max u v)} (x : σ) : x = x ∧ True := ⟨rfl, trivial⟩

theorem bare {α : Type u} (x : α) : x = x ∧ True := ⟨rfl, trivial⟩

theorem umTop {σ : Type (max u v)} {α : Type u} (x : σ) (a : α) : (x = x ∧ True) ∧ (a = a ∧ True) :=
  -- `maxOnly x` alone is the oaiq-124 error: "stuck at solving universe constraint
  -- max ?u.8 ?u.9 =?= max u v"; the universes must be named
  ⟨maxOnly.{u, v} x, bare a⟩

end CD.UM
