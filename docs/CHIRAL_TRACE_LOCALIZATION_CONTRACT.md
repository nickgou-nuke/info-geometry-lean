# Chiral matrix trace and partial-phase localization

Input: `Pasted text(20261028-084629).txt`, 2026-10-28.
SHA-256: `2f5d0cf8b4246c7a0678c656ec9ff47bbbc5e8fb2cf06556316e65eea1755423`.
Base: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
Scope/risk: finite matrix algebra, R2. No diagonalization or ambient matrix
commutativity is assumed. The coefficient ring is commutative for matrix trace.

## Intent and owners

The intake's matrix equations are separated from its spectral-triple and index
interpretations. No new `IsDiracSpectralTriple` or proof-field packet is added.

- `NCG/NonCommutativeFredholmIndex.lean` owns matrix commutators and
  anticommutators. `anticommutator_commutator_of_even` already proves oddness
  of the differential; `commutator_sq_of_anticomm_zero` already proves evenness
  of the square. Its trace/cochain statements remain finite algebraic formulas.
- `Core/PeirceGrading.lean` owns native complementary linear projections,
  `commutator_odd`, `odd_mul_odd`, `mem_even_iff`, and reflection parity.
- `QuantumContext/DrazinSpectralKernel.lean` owns `IsDrazinInverse`,
  `spectralProj`, `kernelProj`, their idempotence, and index-one annihilation.
- Mathlib owns `Matrix.trace`, its cyclic identities and separating pairing,
  `Commute`, `IsIdempotentElem`, `IsSelfAdjoint`, `IsStarProjection`,
  `Matrix.toLin'`, `LinearMap.range`, and `LinearMap.ker`.

Existing related owners inspected include `Core/DiracSuperalgebra`,
`Core/DiracPeirceSuperalgebra`, `Core/PeirceTangent`,
`Core/PeirceMatrixTracePairing`, `OperatorAlgebra/FiniteParitySupertrace`,
`NCG/BlockSupermatrixGradedTrace`, `Canonical/DrazinSupercharge`,
`Canonical/FiniteMatrixGibbsParity`, and `GrandUnification/AnomalyInflow`.
The new statements use an arbitrary full matrix weight rather than the
fixed diagonal parity carrier of `FiniteParitySupertrace`.

## Exact targets and corrections

1. Transport commutators and anticommutators across the trace pairing, and
   prove converses using its nondegeneracy. Anticommutator cancellation needs
   no parity assumption on the test matrix.
2. An idempotent's Peirce pinching is self-adjoint under the trace pairing.
   A weight preserves every pinched trace exactly when it commutes with that
   idempotent. Products of idempotent commutators lie in the existing even range.
3. For C=[F,E], prove [F,C*C]=[[F*F,E],C]. A partial phase does not inherit the
   involution conclusion without controlling its support commutator.
4. A tripotent is its own index-one Drazin inverse. Its square is idempotent;
   if self-adjoint, its square is a native star projection and it satisfies
   F*star(F)*F=F. No identification with sign(D) is inferred for a separate D.
5. Chiral anticommutation plus Drazin commutation makes the regular projector's
   weighted trace zero for additively torsion-free coefficients (used only to cancel two).
   The complementary weighted trace equals trace(γ). For index one, identify
   the complementary projector's actual linear-map range with ker(D).

## Dependency order

These edges are source-level proof dependencies, not a separately formalized
partial order or physical time:

- Cyclic trace -> bracket transport -> cancellation and converses.
- Cyclic trace + existing Peirce projections -> trace adjointness -> pinching criterion.
- Existing commutator oddness + odd-times-odd routing -> quadratic evenness.
- Associative multiplication -> phase commutator defect -> support-commuting case.
- Tripotency -> index-one Drazin witness -> kernel range identification.
- Trace anticommutator cancellation + Drazin commutation + cancellation of 2
  -> regular trace vanishing -> complementary trace localization.

## Unproved interpretation boundary

This change does not establish an unbounded spectral triple, bounded transform,
functional-calculus sign of an arbitrary Dirac operator, heat-kernel theorem,
K-theory class/cocycle normalization, Fredholm index, or Atiyah–Singer theorem.
For general Drazin index k, the complementary range is not asserted to equal
ker(D). The characteristic-two parity converse is not asserted.

## Verification

Pending compilation, axiom inspection, semantic audit, and independent acceptance.
