# Freudenthal mixed-triple realignment

The maintained owners already supply a constructive replacement for the
rank-two mixed-triple and legacy TKK Jacobi counterexamples. This audit reuses
those proofs; it introduces no duplicate charge carrier or assumed Jacobi law.

## Exact replacement

`Exceptional/FreudenthalSymplecticMixedTripleCounterexample.lean` exhibits the
failure of the outer-slot identity required by the legacy mixed TKK lane.
`FreudenthalSymplecticTKKJacobiObstruction.tkk_mixed_jacobi_on_iff_pairing_zero`
characterizes vanishing of one mixed component on a set by pairwise symplectic
orthogonality. This is not full ambient or restricted Lie closure.

On the same `FreudenthalCharge J`, `freudenthalSymplecticTripleSystem D`
packages `symplecticRankTwo D` as a `SymplecticTripleSystemDatum`. Its swap law
has the required correction:

    T(x,y,z) - T(x,z,y)
      = omega(x,z)y - omega(x,y)z + 2 omega(y,z)x.

It also proves first-two-slot symmetry, ternary derivation, and invariance of
the alternating form. It does not assert the false outer-slot symmetry.

On the existing `FiveGradedCarrier D`, `symplecticContactBracket D` changes the
bracket coefficients and interactions. For example, two degree-minus-one
charges bracket to the degree-minus-two generator with coefficient
`-2 * symplecticForm D x y`. The explicit linear representation into
`Module.End ℝ (ℝ × (FreudenthalCharge J × ℝ))` is injective and preserves
commutators. The native `LieRing` and `LieAlgebra ℝ` instances follow from
this representation and the associative endomorphism Lie laws.

These statements assume `AddCommGroup J`, `Module ℝ J`, and the existing
`CubicJordanDatum J`. They do not identify this contact algebra with an
exceptional quartic-derived Lie algebra or rehabilitate `tkkTotalBracket`.
The existing `FreudenthalGlobalJacobiFrontier` explicitly records that boundary.

## Verification

`Exceptional.FreudenthalContactRealignmentAudit` audits twelve declarations,
including the counterexample, constructive triple datum, representation,
native Lie instances, and faithful Lie homomorphism. Parent locked compilation
passed (session 33764, terminal exit 0, 8942 jobs). Independent semantic review
passed; independent QA replay also passed (session 39661, terminal exit 0,
8942 jobs), with all twelve axiom reports using exactly `propext`,
`Classical.choice`, and `Quot.sound`. The audit source has zero warnings;
existing dependencies emit nine warnings plus two package notices. The strict
screen reports zero traps, and scoped diffs are clean.

Session-local logs: `/tmp/freudenthal-contact-realignment-audit.log` and
`/tmp/freudenthal-contact-realignment-qa.log`. Acceptance is limited to this
source-reviewed family, not exhaustive repository coverage.
