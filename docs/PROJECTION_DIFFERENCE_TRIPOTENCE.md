# Projection-difference tripotence contract

The negative owner `Core/NilpotentCartanRegression.mp_difference_not_tripotent`
uses an actual rational Moore–Penrose pair. The existing positive theorem
`Core/NilpotentToCartanDrazinMPPoset.orthogonal_difference` assumes orthogonal
idempotents; `Singular/MoorePenroseSectors` supplies support projections and
the exact square-idempotence defect as the square of their commutator.

The new ring statement is `(p-q)^3-(p-q)=q*p*q-p*q*p`. Thus tripotence is
equivalent to equality of compressions. Commutation is sufficient without
orthogonality. For self-adjoint projections in a normed C-star ring, the
existing square-defect identity and `CStarRing.star_mul_self_eq_zero_iff`
make commutation necessary as well. The MP specialization uses `mp_supports`.

The C-star necessity is not promoted to arbitrary rings or arbitrary star
rings. No new inverse, projection carrier, or spectral classification is
assumed. Maintained source and relevant mathlib searches for tripotence,
compression equality, and projection-difference cubic laws found the cited
owners and no equivalent criterion in the inspected results.

Parent owner build completed successfully (3178 jobs), and parent audit build
completed successfully (3192 jobs); logs are `/tmp/projection-tripotence-build.log`
and `/tmp/projection-tripotence-audit.log`. The audit requests six axiom reports
and contains three examples. Strict screening found zero traps; semantic AA
passed. Independent QA subsequently passed in session 38772: combined
Cobalt/projection audit exit 0, 3195 jobs, recorded in
`/tmp/cobalt-projection-final-qa.log`. Nine combined axiom reports and seven
examples passed; three ring lemmas use only `propext`, and the other reports
use only the standard three axioms. Zero own-source warnings, fourteen
dependency warnings, two package notices; strict screening and scoped diff
checks passed. This accepts the stated classification, not a repository-wide
completion claim.
