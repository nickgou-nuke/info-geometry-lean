# Scope review of GrassmannianBundleCyclotomicOrientability

The current owner was read directly, including its matrix witness and trace
specialization. `Canonical/All.lean` imports it. This is a source review, not
an independent reproduction of the submitted build or axiom-audit report.

The conjugation lemmas prove preservation of idempotence, right invariance,
and a multiplication identity expressing left equivariance. The packaged
theorem does not construct a group, stabilizer quotient, bundle, topology,
or local trivialization. With genuine units, the natural quotient describes
the conjugacy orbit of the reference idempotent, not all idempotents.
The one-sided inverse assumptions in the individual lemmas suffice for
their identities but should not be called a two-sided invertible pair.

The Peirce theorems prove a decomposition, corner square-zero laws, left/right
actions, and that the mixed commutator is diagonal. Their statements do not
construct holomorphic geometry, a cotangent duality, or an Ehresmann connection.
The tracial identity does not require a nondegenerate pairing, so it is not
by itself an adjoint/coadjoint identification. The cubic identity says that
`t^3-t` annihilates the adjoint operation; minimality is not asserted by the
Lean statement (for example a central idempotent has zero adjoint operation).

The final abstract theorem assumes only `Ring A`, square-zero laws, and
`d*B*d=d`, `B*d*B=B`. These describe a reflexive square-zero pair, not a
star-compatible partial isometry. Its active identity is `Δ=d*B+B*d`.
The equations for orders 3, 4, and 6 use this active identity; their ambient
constant term is not necessarily `1`. Exact primitive orders need further
hypotheses and are not consequences of the equations over arbitrary rings.

In particular `Γ^2-Δ=0` is the involution polynomial relation, not `Φ₂(Γ)=0`:
the second cyclotomic polynomial is `t+1`, whereas `t^2-1=(t-1)(t+1)`.
The sandwich identities reversing `Γ` and exchanging supports are algebraic
facts. A Spin/Pin group or a topological orientability theorem is not constructed
by the displayed statements.

These corrections concern interpretation. They leave the underlying Peirce,
trace, cubic, and active-corner polynomial identities available for reuse.
