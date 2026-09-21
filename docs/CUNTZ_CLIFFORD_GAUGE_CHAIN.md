# Cuntz, Clifford, and gauge connections: mathematical dependency order

This reconstruction uses the supplied text as a list of mathematical questions.
The order below is a dependency order for definitions and proofs. It does not
claim to recover an author's hidden reasoning or to derive a physical theory
from similarities between names.

| Structural role | Canonical object | Implemented consequence |
| --- | --- | --- |
| Two commuting actions | The regular bimodule of an associative algebra | The existing `RegularBimoduleCommutant` owner proves the left commutant is the right regular action. |
| A nontrivial clock phase | An invertible Weyl pair inside one algebra | A commuting invertible pair satisfying the phase relation has phase one. |
| Exchange of the two actions | Matrix adjunction on `M₃(ℂ)` | Scalars are conjugated and left multiplication is exchanged with right multiplication by the adjoint. |
| Creation and range splitting | The existing `AlgebraicCuntzNPresentation` | The elements `Sᵢ Tⱼ` satisfy the matrix-unit relations. |
| Finite algebra inside the presentation | A native `AlgHom` from `M₂(R)` | The map is derived from the relations and preserves products and the unit. |
| Split quadratic geometry | The real quadratic form `t² + x² - y² - z²` | All sixteen Clifford anticommutators and a native `CliffordAlgebra.lift`. |
| Transport to Cuntz coefficients | Apply the matrix-unit map to every block | A representation into `M₂(A)` for every real Cuntz presentation, including the algebraic real quotient. |
| Metric adjunction | An additional self-adjoint involution `J = γ₀` | `T ↦ J T* J` reverses products and is involutive. |
| Differential input | Commuting linear endomorphisms satisfying associative Leibniz | A connection `∇ᵢ = δᵢ + L(Aᵢ)` obeys its module Leibniz law. |
| Curvature | The commutator of covariant derivatives | `Fᵢⱼ = δᵢ Aⱼ - δⱼ Aᵢ + [Aᵢ,Aⱼ]` and its action on the module. |
| Gauge transport | An invertible algebra element `g` | `Aᵢᵍ = g Aᵢ g⁻¹ - δᵢ(g) g⁻¹`, connection intertwining, and `Fᵍ = g F g⁻¹`. |
| Finite action | A separately specified cyclic linear functional | The finite sum of `τ(Fᵢⱼ Fᵢⱼ)` is invariant under this transport. |

## Source ownership

The new modules are:

- `InfoGeometry.Algebra.RegularBimoduleWeylObstruction`
- `InfoGeometry.Algebra.CuntzMatrixUnitRepresentation`
- `InfoGeometry.Clifford.CuntzSplitClifford22`
- `InfoGeometry.Geometry.AssociativeGaugeConnection`
- `InfoGeometry.Canonical.CuntzCliffordGaugeChain`

They reuse `Algebra.CuntzN`, `Physics.RegularBimoduleCommutant`, and
`Clifford.Cl11Matrix`. The generic matrix-unit map extends the existing complex
matrix-unit construction to a real algebraic presentation. No replacement
tensor tower, categorical colimit, or purported infinite completion is added.

The real block matrices use the existing atom:

`u = J1`, `v = Eplus`, `w = Eminus`.

Their images under the derived matrix map are exactly
`E₀₁ + E₁₀`, `E₀₀ - E₁₁`, and `E₀₁ - E₁₀`. Thus the representation connects the
concrete matrices to the Cuntz presentation by an algebra homomorphism, rather
than merely checking two unrelated multiplication tables.

## Assumptions and obstructions

The two-generator presentation is the input to the Cuntz results; its matrix
units and Clifford relations are conclusions. Nontriviality is required for
the theorem that the original isometry block fails to be an involution.

A cyclic linear functional on a two-isometry Cuntz presentation satisfies
`τ(1) = 0`. In a nontrivial scalar ring it therefore cannot also satisfy
`τ(1) = 1`. The action is concretely instantiated on the finite real block
matrix algebra with its ordinary four-dimensional trace. It is not extended
to the full Cuntz algebra.

The current complex `CuntzTensorQuotient.dagger_algebraMap` fixes complex
scalars. That owner is an algebraic linear dagger, not a proof of the conjugate
linearity required for a complex C*-adjoint. The new real Clifford construction
does not require that identification. The complex regular-bimodule conjugation
uses Mathlib's actual matrix star.

The connection theorems require the associative Leibniz laws and commuting
base derivatives. These hypotheses are not consequences of the Clifford
relations. A concrete instance takes zero base derivatives and the four gamma
matrices as constant potentials. Its unnormalized finite trace-square action
is 64, and gauge transport preserves it. This number records matrix
normalization; there is no conversion to a chronon, energy, or observable.

The zero potential gives a flat connection on the same carrier, although the
Clifford frame has nonzero commutators. Clifford noncommutativity alone
therefore does not specify the connection or its curvature. Torsion further
requires a soldering form and a differential calculus.

## Boundaries of this implementation

- The matrix adjunction identities are not the general Tomita--Takesaki theorem.
  No cyclic separating vector, modular operator, or analytic modular flow is
  constructed here.
- The Weyl-pair results prove the phase obstruction and commutator formulas.
  They do not identify any finite spectrum with the Riemann zeros.
- The Clifford map is a representation. Its injectivity, a C*-completion, and
  a topological spin-bundle construction are not asserted.
- The chosen action is finite and algebraic. It is neither a Chern--Simons
  integral nor a Wilson-loop expectation, and no Jones invariant is inferred.
- Residues of logarithmic derivatives, convergence of infinite products, and
  the Riemann hypothesis are separate analytic questions.
- For split octonions the correct next object is a derivation satisfying
  Leibniz, including the required associator terms. Associative inner
  derivations proved here must not be transferred to a nonassociative carrier
  without an additional theorem.

## Verification

The narrow workflow uses the repository's unchanged Lean toolchain and
Mathlib revision, checks the full repository import closure of these five
modules sequentially under the shared build lock, and prints the axioms of
every new definition and theorem. It rejects axioms outside
`propext`, `Classical.choice`, and `Quot.sound`.

Its isolated source copy avoids building unrelated repository modules; it is
not a replacement for the repository-wide CI. Reports are attached to the
`Cuntz Clifford Canonical Chain` GitHub Actions run. No dependency manifest,
toolchain, existing verification gate, or build cache is modified by this
change.

Verification status at preparation: kernel checking is in progress. The final
run and its exact commit determine the status; source text alone is not a
verification certificate.
