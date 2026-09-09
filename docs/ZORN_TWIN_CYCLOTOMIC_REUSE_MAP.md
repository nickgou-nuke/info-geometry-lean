# Source-owner search for the twin-Zorn/cyclotomic attachment

Target: `Pasted text(20260906-071521).txt`. Earlier graph and attention attachments
are not substituted for this source. The retained constraints are homogeneous
state representatives, expectation ratios, no primitive spacetime, and the
full nonassociative operator-valued Zorn product including its gauge defects.

Base for this continuation: `projective-graph-hodge-zorn-bilayer`, exact commit
`eb93f7405c2a8e9ad64e15c3bf172317aa960513` (PR #158).
The projective/gauge ancestor is `71e683c8388acfd6101d554aaec0771cc886d2a2`.
Default-branch discovery used `b0fa422e6cb6d3da5be7cbbb5ecfae5c12f3237b`.
No dependency pin, existing source owner, or parent branch is replaced.

## Discovery passes

The pre-code searches included: cyclotomic, cyclotomicProjector,
FiniteCyclotomicProjector, Peirce projector, NCZorn involution, Zorn sheet,
zornFlipOperator, diagonalOperatorZorn, Zorn nucleus, weakValue, rankOne trace,
MatrixStandardForm, and linear antilinear zero. A pull-request search for
cyclotomic Zorn was also performed. This is targeted multi-pass discovery,
not a claim to have inspected every byte of every branch.

Executable source was fetched after discovery. Archived notes, generated
audit reports, descriptions, and theorem names were not accepted as proof.

## Owners reused

- `Physics/NCG/NoncommutativeChiralZornAlgebra.lean`: the actual ordered product,
  both diagonal entries and all six vector entries. This remains the field carrier.
- `Canonical/ThreeColorOperatorCrossCommutator.lean`: ordered cross and dot,
  epsilon tensor, self-cross commutators and full coordinate constructors.
- `Canonical/ThreeColorOperatorSuperBracketClosure.lean`: symmetric cross-defect
  readouts without a falsely installed Lie superalgebra or alternativity law.
- `Canonical/ZornOperatorGradeReversalContract.lean`: an unsigned additive
  sheet-flip involution. Its source does not claim multiplicativity.
- `Canonical/OperatorZornFourPotentialGauge.lean` at the parent: actual
  coefficient derivation, arbitrary direction labels, curvature with both
  associators, and the complete cyclic Akivis source.
- `Canonical/OperatorZornGaugeCovariance.lean` at the parent: coefficient-unit
  gauge changes, inhomogeneous generator term, and covariance on the same carrier.
- `Canonical/OperatorZornRealModule.lean` at the parent: additive real module
  on the same carrier, not an associative algebra replacement.
- `Canonical/CyclotomicProjectorReadout.lean`: existing Fourier-projector data
  and order-two constructor. The new order-four instance discharges its laws.
- `Algebra/CircularChiralOperatorEightBridge.lean`: existing scalar circular
  Peirce basis. No unsupported Weyl-matrix-to-Zorn product identification is added.
- `Analysis/RankOneTrace.lean`: native finite-dimensional rank-one trace API.
  The new complex statement uses Mathlib's same rank-one construction.
- `proofs/SarsModularWeakValue.lean`: a guarded two-coordinate weak value.
  It is not overwritten or totalized; the new trace theorem works for arbitrary
  finite-dimensional complex Hilbert spaces.
- `proofs/KleinBottleSixfoldCyclotomic.lean`: distinct finite and affine glide
  relations, with explicit limits on quotient-topology and modular claims.
- `Topology/DiscreteHodgeDiracBridge.lean`: the two d+delta/d-delta sign
  conventions; its supplied modular-intertwining data is not a new construction.
- `Canonical/PeirceDeWittIdealModularBridge.lean`: concrete two-by-two projector
  arithmetic, not a Tomita commutant theorem despite the filename.

Pinned Mathlib v4.28.1 rank-one, trace, diagonal-power, multiplicative-map,
linear-map and semilinear-map source interfaces were inspected. A newer API
is not substituted silently for the repository pin.

## New local constructions

The continuation constructs the signed exchange automorphism, proves all
three coefficient-nucleus laws, constructs all finite coefficient matrix
Peirce sectors, computes the fourfold Fourier/raising example, and proves the
guarded rank-one trace ratio and independent rescaling invariance. It also
supplies concrete obstructions to the attachment's proposed replacement
product, unsigned multiplicativity, ordinary-commutator shift relation,
diagonal-only reconstruction, and linear/conjugate-linear identification.

These source inspections establish what is implemented, not that the
new or imported declarations have passed native kernel verification.
