# Exact affine analogies and attention fibers

## Provenance and dependency

Source proposal: `Pasted text(20261022-202115).txt`, the analogy/parallelogram
extension. This branch is stacked on PR #189 at commit
`9d3a7c721f2d6f021a8009e461f8181cc67172d1`, not on an assumed merged main.
The existing homogeneous decoder is reused. Probability rows use native
Mathlib `stdSimplex`; independence uses native `AffineIndependent`.

## Source-derived mathematical targets

Indices 0,1,2,3 carry the proposal's man, woman, king, queen labels. The exact
relation V1-V0=V3-V2 is always an explicit assumption; no empirical claim is
made about any trained word embedding or attention value table.

1. The affine weights (-1,1,1) have mass one and reproduce V3. No nonnegative
   probability row on the first three values does so if those three values
   are affinely independent. Without independence the exclusion need not hold.
2. delta=(-1,1,1,-1) has zero mass and belongs to the native homogeneous decoder
   kernel exactly when the parallelogram identity holds. Thus the four indexed
   values are affinely dependent, regardless of ambient dimension.
3. The centered family p(e)=(1/4-e,1/4+e,1/4+e,1/4-e) is a probability row exactly
   for -1/4 <= e <= 1/4. It is strictly positive exactly on the open interval.
   Its members are distinct and have the same readout under the exact relation.
   The two endpoints are the opposite diagonal distributions in the proposal.
4. Normalized readout depends only on the two feature marginals a=p1+p3,
   b=p2+p3: V0+a(V1-V0)+b(V2-V0).
5. The specified boundary heads (0,1/2,1/2) and (1,0,0) reconstruct V3 under
   signed readout 2h1-h2. This is not a statement about arbitrary head pairs.

## Additional proved targets beyond the supplied Lean

- Full kernel classification under an independent first triangle: every
  homogeneous kernel vector is a scalar multiple of delta.
- Under that same condition, equal-mass readouts agree iff both marginals agree.
- Explicit finite-softmax realization of every strictly positive probability
  row using logits tau*log(p), tau != 0, via the existing FiniteSoftmax owner.
- The boundary midpoint head cannot itself be a finite unmasked softmax row.
  Nevertheless strictly positive heads p+=(1/9,4/9,4/9), p-=(2/3,1/6,1/6)
  satisfy 3p+-2p-=(-1,1,1), yielding an exact two-softmax-head signed readout.
- Full marginal coupling coordinates (1-a-b+t,a-t,b-t,t), with exact probability
  feasibility max(0,a+b-1) <= t <= min(a,b).
- For an arbitrary value table, define r=-V0+V1+V2-V3. Perturbing weights by
  e*delta changes readout by exactly e*r, with norm |e|*||r||. The finite Pi
  coordinate norm used by this theorem is Mathlib's default sup norm.

## Boundaries

The supplied hand-written file is not copied as a second decoder or a custom
independence predicate. Its claimed compilation is not taken as build evidence.
A signed output combination is an additional output map, not a nonnegative
attention row. No Markov/Poisson solver property, fixed-query/key realizability,
training convergence, empirical analogy exactness, or speedup is inferred.
Output ambiguity is for the fixed value table; it is not equality of attention
operators on every possible value table. An exact analogy is an exact kernel;
an approximate analogy is a small residual only under a quantified defect bound.

## Verification

Source is a candidate until the scoped workflow succeeds. The workflow builds
the exact repository source closure against the pinned Lean and Mathlib in an
isolated temporary checkout, sequentially under a build lock, then inspects
all new theorem axiom footprints. This is not a whole-repository or Routing.All
build. No root dependency pin is changed and no build cache is deleted.
