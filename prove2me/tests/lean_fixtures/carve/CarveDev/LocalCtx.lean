/-! # CarveDev.LocalCtx: local context a carved file must put back

Auslander–Reiten (oaiq-031, 2026-10-27):
* `local notation "C" => BaseAlgebra k q`, written `Cᵐᵒᵖ` by the section's first declarations: a
  bundle starting with them lost the notation ("Unknown identifier `C`"), the textual use test
  reading `Cᵐᵒᵖ` as one identifier. Here `Cᵒᵖ`, with a local postfix `ᵒᵖ` (lost the same way).
* `local instance … : Module k M` with its Prop partner `local instance … : IsScalarTower k A M`,
  never named by an elaborated term: the partner did not come back with the Module one. Here
  `actHi`/`towerHi` on `Wc n`.
* `local instance (priority := 3000)` put back as `attribute [local instance] N`: the priority was
  lost and the module's `attribute [local instance 2000]` instance won. Here `actHi` over `actLo`. -/

namespace CD.LC

def Opp (α : Type) : Type := α

structure Wc (n : Nat) where
  x : Nat

class Act (α : Type) where
  act : Nat → α → α

class Tower (β α : Type) [Act α] : Prop where
  ok : ∀ a : α, Act.act 0 a = a

def needsTower (α : Type) [Act α] [Tower Nat α] : Nat := 0

section
local postfix:max "ᵒᵖ" => Opp
local notation "C" => Wc 3

def oppSelf (a : Cᵒᵖ) : Cᵒᵖ := a

theorem oppSelf_eq (a : Cᵒᵖ) : oppSelf a = a := rfl

def plainC (a : C) : Nat := a.x
end

section
@[reducible] def actLo (n : Nat) : Act (Wc n) := ⟨fun k a => ⟨a.x + k + 1⟩⟩
attribute [local instance 2000] actLo
local instance (priority := 3000) actHi (n : Nat) : Act (Wc n) := ⟨fun _ a => a⟩
local instance towerHi (n : Nat) : Tower Nat (Wc n) := ⟨fun _ => rfl⟩

theorem tower_use (n : Nat) (a : Wc n) : Act.act 0 a = a ∧ needsTower (Wc n) = 0 := ⟨rfl, rfl⟩
end

end CD.LC
