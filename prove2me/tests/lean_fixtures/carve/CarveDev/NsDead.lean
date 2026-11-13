/-! # CarveDev.NsDead: an empty project namespace that shadows a library one

Jacobsthal (q255, 2026-11-11): vendored modules declared an empty `namespace Erdos970.Asymptotics`.
A module that never saw it wrote `open … Asymptotics` inside `namespace Erdos970`, meaning Mathlib's.
DeclGraph listed an external namespace only when its last component ends some project *constant's*
namespace; the empty project one has no constant, so Mathlib's `Asymptotics` was not listed, and the
carver dropped the token as naming only a dead project namespace ("Unknown identifier `isBigO_iff`").
Here NsDeadA's empty `CD.Dead.Array` and core's `Array`; this module does not import NsDeadA. -/

namespace CD.Dead

open Array

theorem range_zero : (range 0).size = 0 := rfl

end CD.Dead
