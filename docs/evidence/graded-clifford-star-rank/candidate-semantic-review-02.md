# Candidate source-semantic review 02

Reviewer: /root/graded_unroll_intake.

Checkout: /workspace/scratch/9009f3c86480/graded-unroll-extension.

Scope: independent source-only review of the cut-rank owner and two added
adjoint/parity lemmas. No mathematical owner repairs, Lean/Lake execution,
tests, or GitHub writes were performed.

## Exact reviewed identities

| File | SHA-256 |
|---|---|
| lean/InfoGeometry/Clifford/GradedTensorCutRank.lean | 88240ec12d8ae9969ddbe5c8595d8ff0c5c6567f40efedb2825c053e15a39265 |
| lean/InfoGeometry/Clifford/Cl11GradedAdjoint.lean | f2911f2c77dd0ac647e7c46d20754e8dbb984187800c737bc2915dec0598fa7a |
| docs/GRADED_CLIFFORD_STAR_RANK_CONTRACT.md | a68eb6e7c17f55bbd6e95b35ba32ca544607951cda0bf8eff378e9066da12e5b |

The cut-rank owner was read completely. The added headAdjoint_involute and
tensorAdjoint_parity declarations were reviewed with their surrounding
definitions and hypotheses; the earlier adjoint construction was reviewed
in candidate-semantic-review-01.md.

## Verdict

**No mathematical or source-semantic blocker found at these snapshots.**
This remains source-semantic acceptance only. The code was uncompiled at the
time of this review; no execution or axiom-footprint claim is made.

## Canonical contraction and rank

The carrier is the native real algebraic tensor product V ⊗ W. Contraction
is constructed from evaluation into the double dual and the native
dualTensorHom map. Its elementary-tensor value is φ(x) • y, so it is the
actual canonical contraction V* → W, not an arbitrary surrogate.

With finite-dimensional V, contractionEquiv composes native evaluation and
dual-tensor equivalences. Consequently the asserted injectivity is derived
from a constructed equivalence. W is unrestricted throughout this branch.

Cut rank is the real finrank of the actual contraction range. In the finite-left
section the dual domain is finite-dimensional, ensuring the range is
finite-dimensional even when W is not. The right-hand dimension bound adds
finite-dimensionality of W explicitly. The operator-tail bound adds finite
dimension of U and B, retains B as an arbitrary associative real algebra, and
uses its real vector-space dimension. No commutativity of B is inserted.

Subadditivity and monotonicity under independent factor maps are the correct
linear-algebra properties of this rank. The covariance formula uses dualMap
on the left and postcomposition on the right, with the correct order.

## Controlled tensor map

The owner constructs id ⊗ p₀ + T ⊗ p₁ as an actual native tensor endomorphism.
The forward factor-two inequality needs no projection assumptions: it is a
sum of two factorwise maps, each of which cannot increase cut rank.

For the reverse inequality, the hypotheses are T² = id, idempotence of p₀ and
p₁, zero mixed compositions, and p₀ + p₁ = id. These are explicit structural
conditions on the component maps. They do not assert the desired tensor-map
involutivity or either rank inequality. The source derives involutivity by
tensor extensionality and applies the forward bound a second time.

The two natural-number inequalities faithfully express the bounded rank change
without interpreting natural division by two.

## Scope that must remain explicit

This owner proves a general controlled tensor-map estimate. It does not yet
instantiate the complete all-length Jordan–Wigner map, construct its local
cut decomposition, or identify its particular parity projections. It also
does not prove a TT minimality theorem, sharpness of the factor two, or
fixed-total-parity rank invariance. Those stronger source statements remain
outside the present owner. The current header and task contract do not claim
those missing conclusions.

## Added adjoint/parity lemmas

headAdjoint_involute correctly transports the equality that real transpose
commutes with conjugation by the symmetric Eplus involution. It adds a genuine
all-element compatibility statement to the previously reviewed head adjoint.

tensorAdjoint_parity uses the existing tensor-to-matrix parity compatibility
and proves that conjugate transpose commutes with the matrix parity action.
Its coefficient hypothesis θ(star a) = star(θ a) is explicit. This is the
required compatibility condition; the tensor-level commutation is established
by the source rather than assumed.

These additions retain the canonical Clifford star boundary: the custom
transpose-compatible operation is not installed as a global replacement
instance. They add no positivity, norm, completion, or analytic claim.

## Outstanding acceptance

Exact-source closure compilation, native owned-declaration axiom auditing,
review of any further changes/projector owners, and separately reported
integration gates remain necessary. This record does not certify their outcome.
