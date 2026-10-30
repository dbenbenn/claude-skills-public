/-! # CarveDev.SimpBase .. SimpTop: a simp lemma a module never imported, seen in a carved file

oaiq-081 (SubexponentialSAT): a carved bundle or piece holds declarations of many modules, so an
`@[simp]` lemma of a later module (`status_read`) fired in modules that never imported it; `simp`
then closed a goal early and the next tactic failed "No goals" (~40 hand patches). Here SimpLate's
`h_eq` (an attributed declaration, so bundle material) would close SimpUse's `simp` early. -/

namespace CD.Sp

def h (n : Nat) : Nat := n

end CD.Sp
