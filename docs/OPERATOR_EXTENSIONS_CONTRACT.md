# Operator extensions XIV–XVIII: theorem contract

## Intake and scope

Source: `Pasted text(20261028-090911).txt`, SHA256
`4fa5dca9a0bb2db995d899881603d3204b1fc707b5b9b39e6bdbcd5bfde29378`.
The original uploaded text is preserved. The implementation base is PR #232,
commit `423762cd7128ada367735aeb2452f4c53bf192c7`.

The carrier is the full algebra `Matrix n n ℂ` for arbitrary finite `n`.
The native associative Lie bracket is `⁅A,B⁆ = A * B - B * A`.
The star is conjugate transpose; products retain their order. No simultaneous
diagonalization, scalar-matrix restriction, or pairwise commutation of arbitrary
inputs is assumed. Invertibility, idempotence, and self-adjointness are explicit
native hypotheses, or are proved where the input implies them.

This is a finite algebraic extension. It makes no physical, manifold, spectral
limit, point-at-infinity, or differential-equation existence claim.

## Owner map and intended additions

### XIV–XV: Peirce corners and chiral square geometry

Existing owners:

- `Core.PeirceDecomposition.component10 p A = p*A*(1-p)` and
  `component01 p A = (1-p)*A*p`; same-direction products vanish for idempotent p.
- `Core.IdempotentCartan.oddPart`, `evenPart`, and `reflection`; theorems
  `corners_square_zero`, `projection_laws`, `multiplication_rules`,
  `conjugation_on_parts`, `reflection_mul_odd`, `odd_zero_iff_commute`.
- `OperatorAlgebra.MatrixOperatorIdentities.star_lie_of_isSelfAdjoint` and
  `OperatorAlgebra.PeirceTraceGeometry.star_oddPart` from the accepted base.
- `Core.PeirceMatrixTracePairing` and `Core.PeirceMatrixPerfectPairing` already
  own the opposite-corner trace duality; no new corner carrier is needed.

New targets: native bracket root laws, corner trace isotropy and adjoint
exchange, the cross-square formula, and the exact identities for
`M = oddPart p A`, `J = ⁅p,A⁆`:

```
M*M = -(J*J)                         (p idempotent)
M*M = star J * J                     (p star projection, A self-adjoint)
(M*M).PosSemidef
M*M = 0 ↔ Commute p A
Commute p (M*M)
```

Native Mathlib positivity and faithfulness come from
`Matrix.posSemidef_conjTranspose_mul_self` and
`Matrix.conjTranspose_mul_self_eq_zero`.
The correct positivity conclusion is semidefiniteness. Nonzero cross terms
require noncommutation. Bilinear trace isotropy is not Hilbert–Schmidt nullness.

### XVI: native inner Maurer–Cartan one-cochain

`Canonical.FiniteFrameMaurerCartanPolarSplit.leftMaurerCartan G dG` already
means `G⁻¹*dG` for native `Matrix.GeneralLinearGroup n ℂ`, and
`leftMaurerCartan_mul` proves its product cocycle.

The new one-cochain is a native complex-linear map
`ω_G(H) = G⁻¹*⁅H,G⁆ = G⁻¹*H*G-H`, constructed using the native conjugation
algebra equivalence. Its targets are reconstruction, inverse differentiation,
the product cocycle, trace zero, and full Chevalley–Eilenberg flatness:

```
⁅A,ω_G(B)⁆ - ⁅B,ω_G(A)⁆ - ω_G(⁅A,B⁆) + ⁅ω_G(A),ω_G(B)⁆ = 0.
```

The differential is native `LieModule.Cohomology.d₁₂`. The existing
`OperatorAlgebra.DerivationDifferentialForms` has a faithful-action carrier;
the adjoint action of all matrices has a scalar kernel, so no false faithful
instance is introduced. The direction-bracket term is essential.

### XVII: centralizer conservation and quadratic invariance

Use native `Subalgebra.centralizer ℂ (Set.range H)` and its multiplication,
addition and subtraction closure. Do not recreate the commutant.
The previous trace integration-by-parts theorem and native trace duality give
weighted conservation. Existing `Canonical.FiniteMatrixGibbsCentralizer`
already owns the arbitrary weighted-trace/centralizer equivalence.

New substantive target: if `⁅K,H i⁆ = ∑ j, c i j • H j` and
`c i j = -c j i`, prove `Commute K (∑ i, H i * H i)` by finite-sum
cancellation. This does not assume the generators commute and does not store
the conclusion in a structure field. The quadratic element is distinguished
from the double-commutator superoperator:

```
∑ i, ⁅H i,⁅H i,X⁆⁆ = C*X + X*C - 2 • (∑ i, H i*X*H i).
```

Centrality is relative to the named generator family unless that family is
proved to generate the entire matrix algebra.
`trace_star_sum_double_lie` is the full two-input Hilbert–Schmidt
integration-by-parts identity. It does not assert an additional kernel
classification or construct a bundled positive superoperator.

### XVIII: native Cayley domain and transformation

Use native `Invertible`, `IsUnit`, `Units`, and `unitary`, rather than the
attachment's duplicate inverse-pair structures. The algebraic unitarity proof
already exists in `OperatorAlgebra.IndividuatedCayley` and can be specialized
internally with all resolvent fields constructed from native inverse laws.

For `U(X) = (1-X)*(1+X)⁻¹`, the forward domain is `IsUnit (1+X)`.
Parity inversion additionally requires `IsUnit (1-X)`. Targets include
the two resolvent identities, commutation with X, parity inversion, and the
ordered inner-derivative formula:

```
⁅H,U(X)⁆ = -2 • ((1+X)⁻¹ * ⁅H,X⁆ * (1+X)⁻¹).
```

`cayley_units_inv` also proves `U(G⁻¹) = -U(G)` for a native matrix unit G
with invertible `1+G`; it derives admissibility of the inverse input.
`cayley_sub_cayley` proves the genuinely two-input resolvent identity
`U(X)-U(Y) = -2 • ((1+X)⁻¹*(X-Y)*(1+Y)⁻¹)` under the two denominator
hypotheses, with no assumption that X and Y commute.

Every skew-adjoint complex matrix is admissible: the Gram matrix
`1 + star X * X = (1-X)*(1+X)` is positive definite. Derive both unit
denominators, then prove the native unitary membership of the Cayley transform.
The finite value `U(0)=1` and the resolvent identities do not define a point at
infinity. Under the forward domain, `-1` is excluded from the finite Cayley
image over a nonempty complex matrix algebra.

## Noncommuting witnesses

Use explicit nondiagonal 3×3 star projections
`P = (1/9) * [[1,2,2],[2,4,4],[2,4,4]]` and
`Q = (1/9) * [[4,2,4],[2,1,2],[4,2,4]]`.
Certify noncommutation in Lean. Their odd square has a nonzero off-diagonal
entry and a nontrivial kernel: it is nonzero and positive semidefinite, yet
not positive definite. These are witnesses to the general operator theorems,
not substitutes for them.

`MatrixCasimirExamples` supplies a separate three-generator Hermitian family
whose members are all nondiagonal and have nonzero brackets. Its exact skew
coefficient action instantiates the general quadratic-invariance theorem.
The quadratic sum lies in their family centralizer and has entry
`C 0 1 = -32/27`, so it is neither diagonal nor a scalar matrix.

## Dependency order and acceptance

Dependencies will be extracted from constants in kernel-checked declaration
types and values, including generated declarations. The resulting finite DAG,
its reachability order and its Hasse reduction describe these selected proofs.
No analogy is inserted as an edge. In particular, no edge from Peirce
nilpotency to Maurer–Cartan flatness, or from Casimir invariance to Cayley
inversion, is assumed.

Acceptance requires fresh compilation of the selected complete repository
source closure at the pinned Lean/Mathlib versions; a transitive axiom audit;
placeholder, semantic-vacuity and proof-proxy checks; and independent semantic
and verification reviews. Only standard foundational axioms `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Final results and exact
provenance will be recorded after verification; this contract alone is not
proof evidence.
