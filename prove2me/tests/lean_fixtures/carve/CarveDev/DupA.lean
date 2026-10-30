/-! # CarveDev.DupA: a theorem another module (DupZ) declares under the same full name

oaiq-088/090/095/096: OpenAI's sibling modules, never imported by each other, both declare
`OAI.X.lineConvolution_bound` with the same statement, so Lean imports both into the root and keeps
one constant; the name-keyed graph kept one node, and a carved piece holding modules that used
the other copy failed "Unknown identifier" at measure, hours later. DupA has more importers
(DupUseA, DupUseA2), so DupZ's copy is the one renamed. -/

namespace CD.Dup

theorem bound (n : Nat) : n ≤ n + 1 := Nat.le_succ n

end CD.Dup
