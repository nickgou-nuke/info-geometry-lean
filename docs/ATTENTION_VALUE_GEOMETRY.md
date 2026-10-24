# Homogeneous value decoding and Caratheodory attention support

## Theorem contract and source provenance

This extension follows the user attachment `Pasted text(20261022-194609).txt`
and PR #188, inspected against main commit
`f46662884dfc4b063e63157157132ad0fd8758f9`.

Retained mathematics: deterministic routing actions, homogeneous values
(1,v) indexed by Option D, chart normalization, affine independence,
small active simplices, and coordinate uniqueness conditional on a simplex.
The prior routing owner is imported, not copied. GibbsRayGeometry already
owns positive-reference rays and logit shifts; this addition concerns the
linear image of weight vectors in homogeneous VALUE space, a different carrier.

Corrections and additions, distinguished from the supplied code:
- The attachment's Lean code bounds an already independent family but does
  not prove the stated existence of a sparse normalized representation.
- The new existence proof calls Mathlib's Caratheodory theorem and selects
  distinct original token indices in the original positive support.
- The custom ValuesAffinelyIndependentOn predicate is replaced by native
  AffineIndependent. Native Projectivization certifies equality of projective
  points; the attachment's ratio function alone did not construct that quotient.
- Exponentiation of logits is nonlinear. Projective normalization occurs
  after exponentiation and linear decoding; it is not a projective-linear
  map of logits and need not be an invertible projective transformation.
- The d+1 statement preserves one fixed value readout, not the original
  attention row, operator, all possible value tables, or all gradients.

## Exact target

Given V : J -> D -> R, p >= 0 and sum p = 1, there exist r <= card D + 1,
a genuine embedding f : Fin r -> J and strictly positive weights w such that
V o f is affinely independent, every p(f(a)) > 0, sum w = 1, and
sum_a w(a) V(f(a)) = sum_j p(j) V(j).

Support restriction preserves arbitrary masks, including causal masks.
Weights are unique once this independent simplex is fixed. No unique simplex
or shared subset for all queries is asserted. The universal operator barrier
is proved separately: agreement on every value signal implies matrix equality.

The homogeneous decoder is a native linear map. Its kernel is characterized
by zero mass and zero value readout. Nonzero mass proves that the homogeneous
representative is nonzero, and projective_normalization proves equality in
native Mathlib Projectivization. The dehomogenization function itself is total
in Lean; the geometric affine chart is restricted to nonzero mass. Strict
positivity of the finite nonempty softmax partition supplies that restriction.

## Verified source and scope

Verified Lean source commit: `34997f4eea950850014ea190dc73e6c26d407e80`.
Successful workflow: https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/39845024355
Job: `120055932073`; completed on 2026-10-22.

The two new modules and all eight existing repository modules in their
transitive import closure compiled with Lean 4.34.1 and the exact pinned
Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The workflow inspected all 22 new theorem declarations (15 homogeneous-coordinate
lemmas and 7 compression/attention results) using #print axioms. Every result
reported only `[propext, Classical.choice, Quot.sound]`.
The new source scan found no sorry, admit, custom axiom, unsafe or native_decide.

Nonfatal warnings in the new compression file concern letI style and unused
Fintype section assumptions. Existing dependencies retain their own linter
and deprecation warnings. Checkout cleanup reports the pre-existing missing
submodule URL for sandbox/Grassmann.jl; the scoped job still completed successfully.

The workflow compiles unmodified source dependencies in an isolated checkout
of the pinned Mathlib; no root dependency pins or existing owner definitions
are changed. This is not a full-repository or Routing.All umbrella build.

The Caratheodory witness uses classical choice and is noncomputable. This
change does not implement a fast token-selection algorithm or modify Autograd.
The attachment's explicit square-diagonal counterexample and interactive
explorer were not ported in this extension; no new proof of subset uniqueness
or a universal shared sparse subset is claimed.

Canonical full-checkout command:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Projective.AttentionValueCoordinates \
  InfoGeometry.Routing.AttentionValueCompression
```
