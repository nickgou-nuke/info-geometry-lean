# Real Plücker geometry and modular operator boundaries

## Intake and provenance

The user supplied a Bulgarian mathematical stream on 2026-11-12 connecting
affine Plücker coordinates, screws, Schubert charts, Amari potentials, real
Clifford structures, Peirce corners, infinity twistors, and modular dynamics.
Implementation starts from upstream `main` at
`a392af178af1fe2bcba2ba39eb405700c6ee103c`. Existing definitions and their
actual hypotheses determine the theorem contracts below.

The requested scalar field is real. Generic algebra results may use a
commutative base ring but must retain the noncommutative coefficient algebra;
no finite-dimensional restriction is imposed unless explicitly stated.

## Owner search and contracts

| Scope | Existing owners | Intended new implication |
| --- | --- | --- |
| Affine lines and screws in real three-space | `Projective/KleinQuadricPlucker`, `Twistor/PluckerInfinityChart`, `Geometry/PluckerDualFlatBridge` | Fixed nonzero direction gives a linear equivalence between moments and a perpendicular axis point together with pitch; translation preserves pitch. |
| Commutant in the regular representation | `Algebra/AssociativeRegularCommutant`, `Algebra/IdempotentCornerCommutant` | Upgrade the existing set characterization to a native centralizer subalgebra and an algebra equivalence with the opposite algebra. |
| Real infinitesimal generator | `Geometry/AssociativeGaugeConnection`, `Canonical/ModularFlowGeneratorDerivative` | For a skew real complex structure commuting with a self-adjoint generator, the correctly signed product is skew; its inner commutator preserves the complex-linear observable algebra. |
| Analytic integration | `Canonical/TransportLieDerivative`, Mathlib `unitary` and `Unitary.conjStarAlgAut` | In a complete normed real star algebra with continuous star, a skew `J` commuting with self-adjoint `K` yields a one-parameter unitary group and real star-algebra automorphisms with the proved derivative. |
| Infinity-form polynomial and kernel | `Twistor/RealInfinityMatrixPencil`, `Twistor/RealInfinityMatrixPencilBridge`, existing tripotent owners | Distinguish the square-zero flat raised operator from a tripotent, and prove exact consequences in native endomorphism submodules. |
| Choice of information potential | `Geometry/PluckerDualFlatBridge`, `Geometry/DualFlat` | A potential is additional data; the ambient quadratic potential need not be convex after nonlinear chart pullback. |

Each candidate is reviewed before integration. The declaration-level audit
records the final statements and hypotheses; this document does not claim
that a proposed theorem has already compiled.

## Exact constructed interfaces

The moment decomposition is a native `LinearEquiv` for each fixed nonzero
direction `d`: `Vec3 ≃ₗ[ℝ] normalPlane d × ℝ`. Its inverse sends `(p,h)` to
`p × d + h • d`. Perpendicularity is native submodule membership, and both
inverse laws and uniqueness are proved rather than assumed.

The graph-chart result is a native `Equiv` between two-by-two matrices and
normalized Klein coordinates with `p23 = 1`. This is distinct from the
`p01 = 1` independent-coordinate chart used for the potential calculation.
It is not a global affine-line space or a formalized Schubert decomposition.

The positive ambient potential pulled back to the latter nonlinear chart
takes values `10`, `10`, and `25/2` at `(3,0,0,1)`, `(1,0,0,3)`, and their
midpoint. Thus it is not convex. The separately chosen potential
`ψ(u) = (u · u)/2` is strictly convex and has actual Fréchet derivative
`v ↦ u · v`. Its Bregman divergence is the symmetric expression
`((u-v) · (u-v))/2`, vanishing exactly when `u = v`.

The regular representation theorem constructs
`Aᵐᵒᵖ ≃ₐ[R] Subalgebra.centralizer R (range leftRegular)` over a general
commutative scalar semiring and associative coefficient semiring. Its inverse
is evaluation at `1`, followed by `MulOpposite.op`.

The infinitesimal and analytic phase results retain arbitrary
noncommutative coefficient algebras. The restricted derivation is a native
`Module.End` with proved associative Leibniz law; Mathlib's current
`Derivation` API requires a commutative source. The flow is packaged as
`Multiplicative ℝ →* unitary A` and then
`Multiplicative ℝ →* (A ≃⋆ₐ[ℝ] A)`. These flow statements require skew `J`,
but not `J² = -1`; the latter hypothesis is used in the stationary-kernel
equivalence. Algebraic unitarity alone is not asserted to imply norm
preservation in an arbitrary normed star algebra.

## Conventions and rejected identifications

The complex structure `Jc`, Tomita conjugation `JT`, and tripotent `S` obey
different equations: `Jc² = -1`, `JT² = 1`, and `S³ = S`. For the convention
`K = -log ρ`, the real inner generator corresponding to `ρ^(it)` is `-Jc*K`.
Skew-adjointness additionally requires `star Jc = -Jc`, `star K = K`, and
`Commute Jc K`.

The current real infinity-pencil owner proves `N(Λ)² = -Λ • 1` and
`N(Λ) ≠ 0`. Thus its flat member is square-zero and cannot also be tripotent.
Its degeneracy does not construct three spectral projectors or a spacetime
horizon. A tripotent yields those projectors only under its own polynomial
hypothesis.

For this particular pencil, the exact classification is
`N(Λ)³ = N(Λ) ↔ Λ = -1`; at that parameter `1 - N(Λ)² = 0`.
At `Λ = 0`, the zero-color polynomial is the identity, and its range is
provably not the kernel of the raised operator. The matrix carrier here is
four-dimensional over the reals; it is not an eight-dimensional
realification of a complex Lorentzian twistor space.
These theorems concern the direct choice `S = N(Λ)`. A different construction
of a tripotent from additional geometric or spectral data would require its
own definition and compatibility theorem.

Opposite Peirce corners annihilate one another but are generally not each
other's full commutants. The regular left and right representations supply
the relevant commutant theorem. Central elements lie in an algebra and its
commutant simultaneously.

## Explicit remaining scope

No Kerr geometry, quasinormal-mode boundary problem, KMS state construction,
Einstein equation, Lorentzian mass positivity, supermanifold, gauge color
group, or global Schubert decomposition is inferred from these algebraic
results. Clifford parity does not make all odd elements square-zero.
Realification and a split real Klein quadric are distinct constructions.

Information geometry requires a chosen potential with proved regularity and
convexity. The Klein polarity is indefinite. A point outside the Klein
quadric is not thereby a mixed density operator, and quantum relative
entropy is not identified with the Bures metric.

For source context, Adamo's [Lectures on twistor theory, §2.3](https://arxiv.org/abs/1712.02196)
describes infinity-twistor choices, and Witten's
[Notes on Some Entanglement Properties of Quantum Field Theory, §§4.1–4.2](https://arxiv.org/abs/1803.04993)
distinguishes the left/right regular actions, the standard-form modular
operator, and its induced automorphisms. These references motivate the
contracts; neither is substituted for a Lean proof.

## Validation contract

Preserve Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Run the locked root wrapper and
report its actual result. The focused package imports the parent owner files
directly and checks their dependency closure with the same pins, then audits
every new declaration. It does not replace the root gate or certify all
historical files. Placeholder scans, semantic review, and foundational axiom
inspection are separate acceptance checks.
