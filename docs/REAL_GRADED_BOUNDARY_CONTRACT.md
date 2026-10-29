# Lie–Jordan Peirce boundary integration record

## Scope and owners

This integration preserves the repository's existing owner files and imports
the additional generic endomorphism development under
`InfoGeometry.OperatorAlgebra.LieJordanGradedDifferential`. The existing
matrix-specific `InfoGeometry.OperatorAlgebra.PeirceGradedDifferential` remains
unchanged. The incoming modules use the existing Peirce corner and
idempotent definitions rather than introducing replacements.

The native carrier for the generic results is `Module.End R A`, for a
commutative scalar ring `R` acting on an associative, possibly
noncommutative `R`-algebra `A`. The metric-specialized files use full finite
real matrix algebras. These statements do not assert a completed Hilbert
space, an analytic Hodge theorem, or a continuum limit.

## Corrected operator statements

The generalized graded action is defined from an involutive algebra
automorphism `θ` by

```text
twistedInner θ q x = q*x - θ(x)*q
twistedCoInner θ q x = q*x + θ(x)*q.
```

The checked source proves the twisted Leibniz rule and, when `θ(q) = -q`,
the square identity

```text
twistedInner θ q ∘ twistedInner θ q = lieOp (q*q).
```

Thus square-zero follows with the additional hypothesis `q*q = 0`; it is not
claimed for arbitrary `q`. `twistedShortComplex` packages the square-zero
case in Mathlib's `ShortComplex (ModuleCat R)`. The Peirce specialization
derives the relevant oddness and corner nilpotence from the existing
idempotent/reflection structure.

The real matrix metric modules prove their stated finite-dimensional trace
identities under explicit hypotheses. Positivity is not promoted to complete
positivity or to an unnormalized channel theorem. The signed transport owner
keeps its noncommutative sandwich terms and distinguishes the bilinear,
Frobenius, and indefinite pairings.

## Dependency order

```text
LieJordanEndomorphisms
  → LieJordanBoundaryComposition
  → LieJordanGradedDifferential
  → PeirceBoundaryDynamics
  → PeirceBoundaryMetric / PeirceBoundaryOrder
  → PeirceBoundaryWitness

LieJordanBoundaryComposition
  → SignedBoundaryTransport
  → PeirceSignedTransport
  → SignedTransportMetric / SignedTransportOrder
  → SignedTransportWitness

existing Peirce and matrix-tower owners
  → Canonical.LieJordanTensorColimit
```

The two metric/order branches are separate prerequisites where the Lean
definitions do not impose an ordering. This is a local source dependency
summary, not a claim that it is the repository's complete declaration DAG.

## Local verification record

The adapted source closure was built with the repository's serialized Lake
wrapper. The successful command selected 17 modules: the new Lie–Jordan
owners, boundary and signed-transport owners, the colimit bridge, and the
native audit module. `LieJordanPeirceAudit` reported 152 declarations across
its seven explicitly listed owners, including 133 theorem constants. Its
collected axiom set was exactly `propext`, `Classical.choice`, and
`Quot.sound`.

This is scoped module-build and axiom-audit evidence. It is not a full
repository default-target build, and it does not verify the GitHub Actions
workflow execution. The audit module checks the owners listed in its own
source; its counts must not be generalized to every module in the build.
