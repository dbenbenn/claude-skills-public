/-! # CarveDev.SimpRflA .. SimpRflB: an rfl simp lemma of an imported module

q135 (VertexCover, 2026-10-31): `@[simp] theorem tableGraph_tail … := rfl` (Encoding/FinalCNFPattern)
closed the goal of `queryName_correct`'s `simp [...]` in Machines/FinalCNFBase, which imports it;
simp rewrote with it definitionally, so no constant recorded the use, and the carved bundle did not
have it ("unsolved goals"). `other_eq` mentions nothing SimpRflB uses. -/

namespace CD.SR

def f (n : Nat) : Nat := n + 1

def g (n : Nat) : Nat := n + 2

@[simp] theorem f_eq (n : Nat) : f n = n + 1 := rfl

@[simp] theorem other_eq (n : Nat) : g n = n + 2 := rfl

end CD.SR
