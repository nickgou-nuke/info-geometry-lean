# Attention coordinate identifiability and interior fibers

## Provenance and reuse

Source: `Pasted text(20261022-202740).txt` (AttentionSimplexAudit proposal).
This extension is stacked on PR #190, inspected at
`c2793aec5b388c254de8b8a3adc9d3a31e39d7b0`, and thereby depends on PR #189.
Main was also inspected at `c1b4af85f2251c69f9e05c5e0b0f3cf037da1dfe`.
The implementation does not replace current main or merge an earlier branch.

The routing polytope, its extreme points, and deterministic action are already
owned by AttentionPolytope. The homogeneous decoder, coordinate uniqueness,
and affine-independent cardinal bound are owned by AttentionValueCoordinates.
The general inverse-softmax formula is reused from AttentionAnalogyFiber.
No new IsProbSimplex, IsRowStochastic, ValuesAffinelyIndependent, routeMatrix,
or barycentricDecode surrogate is introduced. New probability fibers use
native Convexity.StdSimplex, not the deprecated set-based simplex declaration.

## Source-derived targets and strengthened proofs

The source separates forward readout from inverse coordinate recovery and
supplies uniqueness on the mass-one hyperplane, a conditional feasible null
perturbation, and the explicit collinear values [0,1,2] with rows
(1/3,1/3,1/3) and (1/6,2/3,1/6).

This extension proves the general missing feasibility step: for every strictly
positive finite row p and direction delta, some epsilon>0 makes p+t*delta
strictly positive for every |t|<epsilon. Affine dependence produces a nonzero
delta in the existing decoder kernel. The parameterization is injective and
all sufficiently small displacements have unit mass and the same output.
The main converse shows that uniqueness at any strictly positive probability
row is equivalent to native AffineIndependent of the full indexed value family.
The matrix-level uniqueness theorem only needs row normalization.

For H_V(p)=(sum p, sum p_j V_j), the fiber is the inverse image of H_V(p)
inside the native simplex image. For a strictly positive normalized p:

vectorSpan_R(fiber_V(p)) = ker(H_V).

Thus the actual affine dimension of the probability fiber is

card(J) - finrank_R(range(H_V)).

The attachment states card(J)-card(D)-1 as an exact dimension without an
explicit full-rank hypothesis. Here it is a lower bound (natural subtraction)
in general and an equality when rank(H_V)=card(D)+1. Rank-deficient value tables
can have larger fibers. Strict positivity means relative interior in the
mass-one affine hyperplane; it is not ambient Euclidean interior in R^J.

The collinear counterexample is proved and both rows receive explicit finite
softmax logits. The generic softmax result produces a different softmax row
with the same fixed-value output at any nonzero temperature; ordinary
positive-temperature semantics are its usual specialization.

## Boundaries

The value table is fixed. Equal outputs do not imply equal attention operators
on arbitrary value tables. The new source does not prove fixed-query/key
realizability of the alternative logits, equality of training gradients,
universal cache eviction, algorithmic speedup, or a new sparse implementation.
Masked attention can be studied on its allowed key subtype; strict positivity
on all keys must not be asserted for a masked row. Boundary rows may have
unique representations despite affine dependence.

This change does not reimplement the route-vertex decomposition, formalize the
Python greedy termination bound, or add the causal-route factorial count.
The supplied file's claim of successful compilation is not taken as evidence.

## Verification

The new sources remain candidates until the scoped pinned workflow succeeds.
It compiles the exact transitive repository owner sources sequentially under
a build lock against the unchanged Lean and Mathlib pins, then audits every
new theorem. This is not a full-repository or Routing.All build.

Canonical check in a checkout containing the stacked dependencies:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Projective.AttentionIdentifiability \
  InfoGeometry.Routing.AttentionInteriorFiber
```
