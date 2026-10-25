/-! # CarveDev.Coer: coercion instances that elaborate away, and attributes on imported declarations

* Kirchberg–Rørdam (batch 3, 2026-10-25): `instance : CoeSort CStarPack (Type u)` and the
  `CoeFun` instances of `Channel`/`Flow` leave no constant in the declarations using them
  (`↑p` elaborates to `p.carrier`), so no dependency named them and the bundles lost them.
* A piece re-emitted `attribute [instance_reducible] X` for an `X` a bundle defines: "failed to set
  reducibility status, `X` has not been defined in this file". -/

universe u

namespace CD.Co

structure Pack where
  carrier : Type
  pt : carrier

instance : CoeSort Pack Type := ⟨Pack.carrier⟩

/-- The type `↑p` is `p.carrier`; no constant names the instance. -/
def Pack.first (p : Pack) : p := p.pt

theorem pack_first_eq (p : Pack) : p.first = p.pt := rfl

structure Fn where
  toFun : Nat → Nat

instance coeFnFn : CoeFun Fn (fun _ => Nat → Nat) := ⟨Fn.toFun⟩

def Fn.double : Fn := ⟨fun n => n + n⟩

theorem fn_double_apply (n : Nat) : Fn.double n = n + n := rfl

def rdef (n : Nat) : Nat := n + 1

attribute [instance_reducible] rdef

theorem rdef_pos : 0 < rdef 0 := by decide


class Pos (n : Nat) : Prop where
  out : 0 < n

instance instPosFive : Pos 5 := ⟨by decide⟩

def needsPos (n : Nat) [Pos n] : Nat := n

section
-- Elaborating this binder needs `Pos 5`; no declaration below mentions the binder, so no
-- declaration's constants name the instance (Kirchberg–Rørdam: `variable (h0 : W.x 0 0 * v = v)`
-- needed `NeZero rankNum`).
variable (h : needsPos 5 = 5)

theorem var_user : 1 = 1 := rfl
end

end CD.Co
