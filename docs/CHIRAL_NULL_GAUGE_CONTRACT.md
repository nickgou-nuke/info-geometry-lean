# Chiral null, gauge, conserved-flow and inversion contracts

## Provenance and scope

User intake (28 October 2026): translate the raw horizon/chirality/gravity/modular-flow/infinity narrative into native noncommutative Lean mathematics. The subsequent instruction was to proceed and complete the job. Base inspected: main `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`. This branch is independent of the unfinished Perjes PR #234 and does not claim to repair it.

The intake is retained as interpretation, not promoted to assumptions: gravity as vacuum thermodynamics; mass as chiral interaction; equal gravitational charges attracting; a pole at infinity supplying an opposite charge; mixed states restoring chirality; operator div/curl, Maurer--Cartan frames, modular conservation and Klein/glide spin holonomy. The implementation extracts the precise claims below. It does not derive Einstein's equation, a force law, a thermodynamic horizon, a physical mass-generation mechanism, a Pin-bundle classification or a full Tomita--Takesaki/KMS theorem.

## Owner grounding

- `Core/PeirceDecomposition.lean`: native associative four-corner decomposition and complementary idempotents.
- `QuantumContext/MassAsCommutantCoupling.lean`: grading and sector-swap identities. Its scalar mass-square hypothesis is not inferred for arbitrary couplings; the new matrix realization retains full operator-valued Gramian squares.
- `Algebra/DerivationLieLaneRepresentation.lean`: actual faithful action, Leibniz and commutator laws.
- `OperatorAlgebra/DerivationDifferentialForms.lean`: native low-degree Chevalley--Eilenberg forms, curvature, covariant derivative and Bianchi. New work constructs a pure-gauge connection instead of assuming its Maurer--Cartan equation.
- `SuperGrassmannian/GraphChartTransition.lean`: actual submodules and exact domain of graph inversion. New work specializes this to signed inversion and square-zero obstructions.
- `Canonical/TransportLieDerivative.lean`: actual exponential conjugation and its derivatives. New work derives conservation converses and multiplication/transport consequences.
- `Canonical/ApolloniusMaurerCartan.lean`: its one-Cartan-axis and assigned cycle scope is retained; it is not used as a proof of general noncommutative curvature or a physical source at infinity.

## Mathematical targets

1. Arbitrary rectangular operator blocks B,C: square-zero upper/lower corners, odd doubled coupling, square diag(BC,CB), and Hermitian specialization diag(B B*,B* B). No scalar mass-square reduction or commutativity of blocks is imposed.
2. Explicit parity averaging in a real algebra: invariance, idempotence, fixed-point criterion and removal of odd components. This is a specified averaging map, not a claim that every mixed state is symmetric.
3. For a native derivation lane and a unit g, construct theta_g(D)=g^-1 D(g), prove the inverse derivative, the product law, Maurer--Cartan flatness, and exact covariant transport. The full bracket-of-directions term is retained.
4. Matrix inner divergence and curl: derive commutator defects and trace conservation. A nonzero positive Gramian cannot equal a sum of finite matrix commutators. A boundary/completion is additional data, not produced by an inverse symbol.
5. Actual graph submodules and signed exchange J(v,w)=(-w,v): J^2=-I on vectors, but the corresponding double map fixes every submodule; invertible graphs map to negative inverse graphs. A nonzero square-zero endomorphism exits the graph chart. Clifford-null-to-square-zero uses the native Clifford relation, not determinant rhetoric.
6. Existing exponential flow: all-time fixedness iff commutation with its generator, polynomial/product preservation, and conserved projectors. Only a specified finite twisted trace identity is called twisted cyclicity; positivity and analytic KMS are separate.

## Dependency poset

`Peirce/block algebra -> chiral coupling -> Gramian/trace obstruction`

`native derivation action -> inverse derivative -> pure-gauge one-form -> Maurer--Cartan -> covariant frame transport`

`native graph transitions + Clifford relation -> null/invertibility obstruction -> signed inversion charts`

`existing exponential transport + derivative uniqueness -> conserved operator algebra`

The branches share operator carriers but none is asserted to imply a gravitational field equation or a topological charge at infinity. The formal source imports and theorem applications, not analogy, define the edges.

## Verification

All code must compile in the pinned Lean/Mathlib environment with no proof holes, no custom axioms and no unsafe/native decision shortcuts. `tools/quality/check_chiral_null_gauge.py` builds the exact source closure serially and invokes Lean's public transitive axiom collector. Its result is scoped to the listed six owner modules; it is not a root-package build. Dependency pins and existing modules are left unchanged. The six owner modules have passed the repository's locked Lake build. The source-closure and transitive axiom audit is tracked separately by the checker and must pass before this contract is treated as fully verified.
