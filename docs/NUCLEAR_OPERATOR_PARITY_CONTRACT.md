# Nuclear operator, five-grade, and parity contract

Source revision: `00b41c37ad68b0dd24690be03ab8c714365ffb5f` of
`nickgou-nuke/info-geometry-lean`, inspected through GitHub and an independent
checkout. Lean remains 4.34.1; mathlib remains
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Intake and mathematical carriers

The current intake connects five-grade symmetry, supercolor and Grassmannian
structures, nuclear quantum-number operators, tetraktys, RPA and Soloviev
operators, chiral parity, the horizon zero-mode carrier, isospin, mass, and spin.
The exact intake is preserved in the work record. The earlier operator-stream
checkout and delivered proofs remain separate and unchanged.

The coefficient carrier is an arbitrary associative `Ring A`. Five-projector
owners use `Algebra ℝ A`; this is the native scalar action, while all operator
coefficients remain elements of `A`. Endomorphisms use native `Module.End`;
two-sector blocks use the existing native `Matrix (Fin 2) (Fin 2) A` owner.
Raw nonassociative Zorn multiplication retains its separately proved product
and parity actions. No associative ring instance is imposed on raw Zorn data.

## Selected proof targets

1. Derive a tripotent from the two actual diagonal color idempotents. With
   the existing common-source hypothesis, identify the reverse products of
   the intercolor matrix units and their native tetraktys mass/spin operators.
   Keep the two-color support `Eᵢᵢ + Eⱼⱼ` as an operator. Connect its zero
   complement to the five-grade parity owner below.
2. For a tripotent `t`, its existing zero projector `P₀ = 1 - t*t`
   supplies an idempotent. Its Peirce odd component is exactly the sum of
   adjoint grades −1 and +1; its even component is the sum of −2, 0, and +2.
   Conjugation by the existing involution `invS P₀` realizes these signs.
3. Derive total Soloviev parity invariance from those actual grade memberships,
   using `NuclearOperatorSuperSoloviev` and the existing
   `NuclearSuperSolovievPeirceBridge` carrier. Derive admissible blocks by
   applying the existing five projectors to arbitrary operator coefficients.
4. For the signed full-operator block `[[A,B],[-B,-A]]`, retain the commutator
   in its square. Prove the exact Hadamard intertwining with the off-diagonal
   block whose ordered factors are `A-B` and `A+B`, and the resulting parity
   and product identities. Reuse `blockHamiltonian` rather than inventing a
   second matrix carrier.
5. Extend the existing phonon Hamiltonian to arbitrary operator coefficients
   `Ω_i : A`. Prove its full commutator, including the terms
   `[Ω_i,X] * numberOp i`. In particular, creation has both the mode term and
   the coefficient-commutator correction. Conservation of a quantum-number
   operator is an explicit commutator equation.
6. From `Γ*T = -T*Γ`, derive the polynomial projector intertwiners. The zero
   projector commutes with `Γ`, while positive and negative projectors exchange.
   Use the existing native zero-mode restriction to prove that `Γ²=1`
   restricts to an involution on `ker T`.

## Dependency order and distinctions

Tripotent polynomial projectors precede the five adjoint components. Their
parity coarsening precedes the Soloviev invariance theorem. The independent
square-zero/Peirce tetraktys owners supply operator-valued quadratic and
commutator generators. RPA block products and operator-weighted phonon
commutators are separate constructions joined only through explicit maps.

Parity coarsening preserves each five-grade sector. Reversing grades requires
an actual automorphism sending the grading element to its negative. A generic
supercolor index is not identified with an integer five-grade label.

For the two-color tripotent `T = Eᵢᵢ - Eⱼⱼ`, the selected intercolor units
have grades `±2`. They are odd at the cut `Eᵢᵢ` and even at the distinct cut
`P₀ = 1 - Eᵢᵢ - Eⱼⱼ`. The Soloviev grade-`±1` channels use their stated
native range hypotheses or are constructed by the corresponding projectors.

Existing operator anchors include `Core.SuperGrassmannianSusy`,
`Core.SupercolorMultiplication`, `Core.SupercolorSourceClosure`,
`Physics.Cl55SpinorCartanFock`, `Physics.NuclearOperatorSuperSoloviev`,
`Physics.NuclearPhononRPAAlgebra`, `Core.TripotentEigenspaces`, and
`Physics.Algebra.TripotentInvariantCarrierBridge`. Their precise theorem
types and representation hypotheses govern every application.

## Acceptance

Only complete native Lean proofs are promoted. No custom axioms, proof holes,
surrogate scalar coefficients, hidden desired-conclusion fields, or global
commutativity assumptions are introduced. Builds are serialized under the
shared lock. Generation, source review, and final axiom acceptance use separate
roles. Final acceptance covers all 45 new theorems, three definitions, and
13 reused interfaces. The complete 92-source integration closure compiled,
all 34 integration checks passed, and both independent axiom audits accepted
their assigned declarations. The checked axiom union is exactly `propext`,
`Quot.sound`, and `Classical.choice`; frozen manifests record every source and
the exact hypotheses in each elaborated signature.
