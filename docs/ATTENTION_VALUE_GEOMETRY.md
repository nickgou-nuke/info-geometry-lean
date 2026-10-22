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

## Scope and validation

The two new Lean sources are candidates until the scoped workflow succeeds.
The workflow compiles unmodified source dependencies against the exact
repository Mathlib commit and Lean toolchain, then prints the axiom footprint
of every new theorem. This is not a full-repository or Routing.All build.
No root dependency pins are changed.

The Caratheodory witness uses classical choice and is noncomputable. This
change does not implement a fast token-selection algorithm or modify Autograd.
