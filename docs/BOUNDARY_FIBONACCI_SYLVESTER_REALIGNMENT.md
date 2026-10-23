# Boundary/Fibonacci prescribed-defect resolution

## Ground-truth theorem contract

The carrier is the existing `Matrix (Fin 2) (Fin 8) ℂ`, with ordinary
matrix multiplication acting on column vectors. The owner
`Canonical/BoundaryFibonacciIntertwinerObstruction.lean` defines
`firstGeneratorDefect T = T * s0 - R * T` and `secondGeneratorDefect`.
It proves `firstGeneratorDefect_ker_eq_bot` using the actual boundary
relation `s0 * s0 = -1` and the actual Fibonacci theorem
`YangBaxterProof.det_R_sq_add_one_ne_zero`.

The constructive alternative is the inhomogeneous Sylvester problem:
every prescribed first-generator defect Y has a unique solution,
`T = -(R * R + 1)⁻¹ * (Y * s0 + R * Y)`.
The simultaneous two-generator problem is solvable precisely when its
second prescribed defect equals the second defect of this recovered T.
This gives an explicit compatibility criterion, not a nonzero homogeneous
intertwiner. It changes no carrier, representation, generator, or phase.

The existing horizon owner transports the homogeneous obstruction to linear
maps. The quotient-factorization owner gives conditional descent, not a
solution of arbitrary prescribed defects. The new focused owner imports the
matrix obstruction and Mathlib's finite-dimensional injectivity/surjectivity
result. Its audit companion checks the resulting theorem axioms.

No equivalence of the braid representations, arbitrary two-defect
surjectivity, or categorical/continuum identification is asserted.
## Verification

The locked build of `BoundaryFibonacciSylvesterResolutionAudit` and
`BoundaryFibonacciQuotientFactorization` passed (8,993 jobs). The five new
lemmas report only `propext`, `Classical.choice`, and `Quot.sound`.
Strict OpenGauss screening and semantic-vacuity screening reported zero
findings. Existing dependency warnings and two pre-existing horizon `simpa`
warnings remain; no warning-free repository certification is claimed.

Independent A-A Ptolemy passed the final source review. Independent QA Curie
reran the locked targets and screening and passed this patch; its audit
output was cache-replayed against unchanged source hashes. The earlier
read-only QA role withheld acceptance because its role prohibited builds;
Curie's separate execution supplied that missing check.

The repository-wide counterexample inventory and constructive-replacement
programme remain incomplete. This record covers only the named source files.
