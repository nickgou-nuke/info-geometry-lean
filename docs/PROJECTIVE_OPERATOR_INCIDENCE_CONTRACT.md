# Projective operator incidence: theorem contract

## Provenance and scope

Input: David Braun, Nicolas Magaud, Pascal Schreck, *Two Cryptomorphic
Formalizations of Projective Incidence Geometry*, HAL-01887000, uploaded PDF,
23 pages. The intended mathematical input is the incidence/rank dictionary,
the rank inequalities, closure, and nondegenerate point/line constructions.

Upstream inspected: `nickgou-nuke/info-geometry-lean`,
`b143075bbf27e75860a1011e04423a0f227b7c41`.
Toolchain: Lean `v4.34.1`; mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

This development constructs the representable geometry of a finite-dimensional
inner-product space inside its full operator algebra. It does not claim the
paper's abstract cryptomorphism for arbitrary incidence structures.

## Actual carriers and conventions

- Points: native `Projectivization K V`, with its existing quotient and
  `Projectivization.submodule`.
- Linear/projective rank: `Module.finrank K` of the span of the point subspaces.
- Lines: submodules of vector-space dimension exactly two.
- Operator carrier: the full noncommutative algebra `E →L[𝕜] E`, with
  `𝕜` real or complex and ordinary composition as multiplication.
- Projection carrier: native subtype of operators satisfying
  `IsStarProjection`, i.e. self-adjoint idempotents.
- Geometry-to-operator map: `Submodule.starProjection`; inverse: operator range.
- Incidence: inclusion of subspaces, equivalent to absorption under operator
  multiplication. No global commutativity hypothesis is imposed.
- Finite-dimensional hypotheses are explicit wherever natural-number rank is
  used. Projective plane means vector dimension three; projective three-space
  means vector dimension four.

## Source-confirmed owners and exact interfaces

Existing repository owners inspected:

- `OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean` exposes
  `Submodule.starProjection` and proves its range, kernel, fixed-point,
  idempotence, and orthogonal-complement identities.
- `OperatorAlgebra/ComplexBoundedOperators/AdjointProjection.lean` exposes
  `IsStarProjection` for those operators.
- `Canonical/RealStageProjectionMurrayVonNeumann.lean` uses
  `LinearMap.IsStarProjection.ext` to identify projections by their ranges;
  its rank classification concerns Murray-von Neumann equivalence, which is
  distinct from incidence of specific subspaces.
- `Projective/ExteriorKleinTwoPlaneIncidence.lean` proves real two-plane
  incidence equivalent to a vanishing exterior product. This is a separate
  geometric representation, not a generic point/rank interface.

Native mathlib interfaces reused directly to keep imports narrow:

- `Projectivization.equivSubmodule : Projectivization K V ≃
  {H : Submodule K V // Module.finrank K H = 1}`.
- `Projectivization.finrank_submodule`, `submodule_injective`, `mk''`, and
  `submodule_mk''`.
- `Submodule.range_starProjection`, `starProjection_eq_self_iff`, and
  `starProjection_comp_starProjection_of_le`.
- `ContinuousLinearMap.IsStarProjection.ext_iff`: star projections are equal
  exactly when their ranges are equal.
- `Submodule.finrank_sup_add_finrank_inf_eq`: the dimension modular identity.

The source-confirmed gap addressed here is the reusable connection from native
projective points and their rank geometry to arbitrary orthogonal-projection
operators, including the failure of multiplication to represent intersection
without commutativity.

## Intended theorem dependency order

1. Native subspaces and orthogonal projections give inverse carrier maps.
2. Subspace inclusion is equivalent to operator absorption in both orders.
3. Projection multiplication represents intersection precisely in the
   commuting case; the ambient algebra and projection family remain general.
4. Finite joins of point subspaces give rank normalization, monotonicity,
   subcardinality, and submodularity.
5. Rank-preserving insertion is equivalent to incidence with the existing span.
6. Distinct points generate a unique dimension-two line; ambient dimension
   controls whether two lines must intersect.
7. Isometric conjugation preserves the operator and geometric constructions.
8. A proved noncommutativity result witnesses the limits of replacing meets
   by products.

This is a dependency order of mathematical statements. It is not an assertion
of physical causation or a new theory of causality.

## Specification checks

- Do not measure the rank of a family of projective points by the vector-space
  span of their projection MATRICES. Use the span of their ranges.
- Do not identify arbitrary idempotents from their ranges. Self-adjointness is
  essential for this carrier equivalence.
- Do not assume distinct vectors define distinct projective points.
- Do not assert uniqueness of a line for repeated points.
- Do not assert arbitrary lines intersect in higher-dimensional projective space.
- Do not use arbitrary invertible conjugation to preserve orthogonal
  projections; isometric/unitary conjugation preserves the adjoint.
- The printed four-point rank upper bound in Table 14 is already implied by
  subcardinality. It cannot establish exact projective dimension three.

## Verification boundary

All new theorem-bearing source must be compiled with the pinned Lean/mathlib,
under the shared build lock, and audited for placeholders and nonfoundational
axioms. Compilation establishes the exact Lean statements. An independent
semantic review must also check the source-to-statement correspondence.

The environment uses a source snapshot of the inspected upstream files and
reads the already available pinned mathlib cache. No dependency revision or
upstream manifest is changed. Full-repository build status is separate from
the checked new import closure.
