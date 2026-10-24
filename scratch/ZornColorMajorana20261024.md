# Zorn color Majoranas: uncompiled contract

Imports target the expected native ZornSignedCAR and ZornColorParity (v3
scratch APIs inspected), plus existing ZornLeftGrading. Those first two native
paths were absent at authoring time. Parent must promote/repair them before QA.
No builds, tests, CAS, or live edits performed. These are candidates, not receipts.

Convention Q=L(U), Qstar=L(-V): Mplus=Q-Qstar=L(U+V),
Mminus=Q+Qstar=L(U-V). Arbitrary CommRing, no inversion of two or star claim.
Core candidate contains squares +1/-1, all mixed anticommutators zero,
distinct same-sign anticommutators zero, parity=Mminus*Mplus, four directed
flip laws, interleaved six-product=+L(diagonal 1 (-1)), odd/tangent equations.
The six-factor order is explicit and must not be silently permuted.

Reuse search: ZornLeftCAR's Clifford/square API is real-specialized;
BosonMajoranaFermionTransmutation's results act on dressed commuting-boson
systems, not these primitive Zorn operators; CliffordCARProjectors uses its
Clnn carrier. No such carrier or structure is introduced here. Generic
alternative L_map square/polarization and native grading/parity are reused.
Element-side reductions use native dot/cross multiplication only.

Companion ZornColorMajoranaSums20261024.lean targets native
InfoGeometry.Algebra.ZornColorMajorana. It contains total sum squares ±3,
mixed anticommutator/oddness and the two identical-sign rotation actions.
No gl(3|1) identification or faithfulness theorem is asserted.
