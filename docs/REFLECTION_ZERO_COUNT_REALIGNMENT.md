# Finite reflection zero counts

## Ground-truth contract

`Arithmetic/SarnakLocalCertification.lean` owns the actual complex reflection
`critical_reflection z = 1 - star z`, its involution theorem, and
`RiemannSymmetric f` (reflection preserves the zero predicate).
Its polynomial `z * (z - 1)` refutes confinement from symmetry alone.
`ZetaSymmetryHeuristicComplement.lean` has a separate centered-even
counterexample. Neither symmetry is a proof of the Riemann hypothesis.

The alternative is exact finite counting on the original complex carrier.
For a finite reflection-invariant set, reflection bijects points below and
above real part 1/2. The total count is the on-line count plus twice the
below-line count. Consequently an odd finite count forces an on-line point.
For a reflection-invariant finite region and a `RiemannSymmetric` function,
apply this result to the region's zero filter. These are counts of distinct
points, not analytic multiplicities. No finite coverage or odd zero count
is assumed to hold for the actual xi function without separate evidence.

Reuse: Mathlib `Finset.card_bij`, `card_filter_add_card_filter_not`, and the
owner's reflection involution. Existing local certificates and orbit lemmas
remain intact. New results are consumed by the existing Sarnak test surface.

## Verification

The locked `InfoGeometry.Arithmetic.SarnakLocalCertificationTests` build
passed (8,937 jobs), including the new owner and two concrete examples.
All five new declarations report only `propext`, `Classical.choice`, and
`Quot.sound`. Strict OpenGauss screening reported zero traps for the owner
and tests; semantic-vacuity screening reported zero findings for the owner.

Independent A-A Carson passed the source review, including the final
singleton-filter tactic adjustment. Independent QA Averroes reran the locked
build and screening and accepted this limited scope against unchanged source
hashes; the QA build replayed cached compilation and axiom output.
Existing dirty-dependency notices, upstream warnings, and five warnings in
unchanged test proofs remain. The new owner and examples have no warnings.
This is not a warning-free repository certification. The repository-wide
counterexample replacement objective remains incomplete.
