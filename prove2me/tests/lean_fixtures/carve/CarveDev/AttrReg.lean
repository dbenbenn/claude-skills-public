/-! # CarveDev.AttrReg: a standalone attribute command whose targets a bundle already registered

q141: `attribute [aesop …] X Y` after shim lemmas came back in every file keeping a declaration of
its section; a piece importing the bundle that declared (and registered) X ran it again, and aesop
refuses a rule registered twice ("rule … is already registered"). `symm` tolerates it, so here the
carved text shows the repeat. -/

namespace CD.AR

def R (a b : Nat) : Prop := a = b

def S (a b : Nat) : Prop := a = b

theorem R.flip {a b : Nat} (h : R a b) : R b a := Eq.symm h

theorem S.flip {a b : Nat} (h : S a b) : S b a := Eq.symm h

attribute [symm] R.flip S.flip

section L

attribute [local symm] R.flip

theorem useR (h : R 1 2) : R 2 1 := by symm; exact h

end L

theorem useS (h : S 1 2) : S 2 1 := by symm; exact h

theorem useRS (h : R 1 2) (h' : S 1 2) : R 2 1 ∧ S 2 1 := ⟨useR h, useS h'⟩

end CD.AR
