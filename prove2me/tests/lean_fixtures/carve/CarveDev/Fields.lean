import CarveDev.Base

/-! # CarveDev.Fields: identifiers that do not denote what a lexical reading of their text says

* PosteriorReplicas (2026-10-23): `(E.rules ω).fixed_quadratic_memory` reported the field token
  `fixed_quadratic_memory`, read in its namespace as the different theorem
  `OAI.PosteriorRegression.fixed_quadratic_memory`: a false `import Theorems.*` edge.
* Problem355 (2026-10-23): renaming `AuxiliaryZeroCount.weighted_count_le_log` also renamed the
  reference `ZeroGlobalCount.weighted_count_le_log` inside it.
* PermanentBorder (2026-10-23): renaming `HasBorderDeterminant.coefficientPolynomial` also renamed
  the definition `coefficientPolynomial` in its own statement. -/

namespace CD

theorem fqm : True := trivial

structure Inner where
  val : Nat

theorem Inner.fqm (i : Inner) : i.val + 0 = i.val := rfl

structure Outer where
  inner : Nat → Inner

theorem Outer.fqm (o : Outer) : (o.inner 0).val + 0 = (o.inner 0).val := (o.inner 0).fqm

theorem outer_dot (o : Outer) : (o.inner 0).val + 0 = (o.inner 0).val := o.fqm

namespace ZG

theorem wcl : 0 + 0 = 0 := rfl

end ZG

namespace AZ

theorem wcl : 0 + 0 = 0 := by
  apply ZG.wcl

end AZ

def cp (n : Nat) : Nat := n

theorem Outer.cp (o : Outer) : cp (o.inner 0).val = (o.inner 0).val := rfl

theorem uses_outer_cp (o : Outer) : cp (o.inner 0).val = (o.inner 0).val := o.cp

/- Names that declare or name a case are not references: the carver must never write them in full
(RationalHitting 2026-10-24: the constructor `| transfer (a b : K) …` of `Eval`, also the name of a
definition, became `| _root_.….Eval.transfer`; PermanentBorder: `| zero =>` of `induction … with`
became `| _root_.Nat.zero =>`, "Invalid alternative name"). -/

def transfer (n : Nat) : Nat := n

inductive Step : Nat → Nat → Prop where
  | transfer (n : Nat) : Step n (transfer n)

inductive Tree where
  | leaf
  | node (l r : Tree)

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

namespace Other
def leaf : Nat := 0
end Other

open Other in
theorem Tree.size_pos (t : Tree) : 0 < t.size := by
  induction t with
  | leaf => exact Nat.one_pos
  | node l r hl _ => simp only [Tree.size]; omega

open Other in
theorem Tree.size_pos' (t : Tree) : 0 < t.size := by
  cases t with
  | @leaf => exact Nat.one_pos
  | @node l r => simp only [Tree.size]; have := Tree.size_pos l; omega

end CD
