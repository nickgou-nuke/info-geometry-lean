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

Verified source commit: `0350ab7050cbdb82984fcfddfda7116c3489b6cb`.
Successful scoped workflow:
https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/39879626170
Job `120173596734`, completed on 2026-10-23.

Both new modules compiled with Lean 4.34.1 and exact Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All eight existing repository
modules in the transitive import closure were compiled from unchanged owner
sources before their dependents. The audit checked all 29 new theorem
footprints (13 in AttentionIdentifiability and 16 in AttentionInteriorFiber).
Every footprint is `[propext, Classical.choice, Quot.sound]`.
The new sources contain no `sorry`, `admit`, custom axioms, `unsafe`, or
`native_decide`. The subsequent documentation commit does not change Lean.

This is scoped verification, not a full-repository or Routing.All build.
The separate unchanged `post-build-gate.yml` workflow reports failure on the
same source commit (run 39879624740); it was not diagnosed or repaired here.
No claim is made that all repository CI checks are green.

Nonfatal warnings in the new sources: an unused `not_imp` simp argument,
an unused Fintype D section assumption on rank-nullity, and a letI style
warning. Existing dependencies retain their prior deprecation/style warnings.
Checkout cleanup reports the existing missing submodule URL for
`sandbox/Grassmann.jl`. The first attempt stopped before Lean because checkout
performed that cleanup early; the workflow now removes its local read-only
credential without traversing submodules. The second attempt exposed one
scalar cancellation proof error, corrected in the verified source commit.

The scoped workflow uses an isolated temporary checkout of the exact Mathlib
pin, compiles sequentially under a build lock, and checks the complete new
axiom-output count and allowed axiom set. No root dependency pin is changed,
no cache is deleted, and no training code is modified.

Canonical check in a checkout containing the stacked dependencies:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Projective.AttentionIdentifiability \
  InfoGeometry.Routing.AttentionInteriorFiber
```
