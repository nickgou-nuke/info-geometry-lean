# Existing adjoint and covariance repairs: source audit

This batch verifies existing owner proofs rather than adding parallel
definitions. Source and reference searches covered the declarations below
and their maintained Lean uses. It is not an absence claim for the repository.

## Moore–Penrose transport

`Singular.MoorePenroseTransport` transports the four Penrose equations through
an arbitrary ring equivalence when the target involution is transported too.
With a fixed involution, preservation for a specific pair requires exactly
self-adjointness of the two mapped support elements. Under invertible
similarity this is equivalent to both source supports commuting with `star g*g`.
Given an actual target inverse, uniqueness turns this into the exact equality
or inequality criterion for that inverse. Nonunitary similarities are allowed
when the local Gram commutations hold; no target-inverse existence is inferred.

## Dirac solder adjunction

`CliffordWeyl.DiracSolderAdjoint` proves metric-twisted adjunction exchanges
the two spinors when the metric is Hermitian and involutive. Its native
finite-spin metric and noncommuting ket–bras witness failure of ordinary
adjunction to perform that exchange. This is not a positive inner-product
or octonion-multiplication identification.

## Incidence isotropy

`Twistor.TwoTwistorIncidenceIsotropy` proves that the specified incidence
equation and total isotropy, with an invertible frame, imply `Xᴴ*X=1`.
Hermiticity is instead equivalent to the frame-skew condition
`Pᴴ*Ω + Ωᴴ*P = 0`. The native `i I` example separates the two properties.
Both conditions together force the reconstructed node to square to one.
No assertion is made that isotropy alone gives a Hermitian spacetime node.

The separate `MarkovPetzPositivityBoundary` was also inspected: it already
has the complete positivity-preservation-versus-symmetry iff for idempotent
real sandwiches and its own audit. It is not duplicated in this batch.

Parent verification passed for seventeen selected declaration heads and two
derived examples in `Canonical.AdjointCovarianceRealignmentAudit` (locked
session 3534, 3188 jobs, `/tmp/adjoint-covariance-audit.log`). The selected
heads' transitive axiom union is `[propext, Classical.choice, Quot.sound]`;
`IsMoorePenroseInverse.map_iff` uses no axioms. The new audit emits no warnings;
the log retains 24 existing dependency-source warnings and two package notices.
Strict OpenGauss screening reports zero traps, and the scoped staged diff
check passes. Independent owner-level semantic and artifact reviews passed.
Independent kernel QA also passed (session 92533, 3188 jobs,
`/tmp/adjoint-covariance-qa.log`), confirming all seventeen reports, both
examples, and the same warning scope. This acceptance covers these selected
declarations and examples, not an exhaustive repository audit.
