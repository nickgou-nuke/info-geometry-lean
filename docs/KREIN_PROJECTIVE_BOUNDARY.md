# Native projective Krein boundary

## Construction and dependency order

The earlier bounded realization fills the algebraic and Krein compatibility
packets. This layer supplies their missing **actual projective ray carrier**.

1. `Krein/StateNullCone.lean` reuses `KreinStateSpace` and its existing
   `NullCone`, both built on Mathlib's `Projectivization`. It proves that a
   nonzero vector represents a null ray exactly when `kreinInner x x = 0`.
   It does not define a second cone or substitute a positive norm.
2. For the existing `AlgebraicDrazinData` with complement `H`,
   `KreinProjectiveBoundary.projectiveBoundary` is the intersection of this
   null cone with the projective lines contained in `ker (H - 1)`.
3. `mem_projectiveBoundary_mk_iff` characterizes membership by
   `H x = x ∧ kreinInner x x = 0`. Using the owner's derived idempotence of
   `H`, `mem_projectiveBoundary_iff_range` identifies the same carrier with
   the projectivization of `range H ∩ Null`.
4. `nativeBoundary` constructs the existing `DrazinKreinNullBoundary` packet
   with this subtype of `Projectivization ℝ Space` as `Ray`. Its representative
   is Mathlib's chosen nonzero representative. All packet conditions are
   proved, and `nativeBoundary_rep_recovers_ray` proves that projectivizing
   the selected representative returns the original ray.

Thus rays really identify nonzero scalar multiples. Choosing representatives
for the legacy packet does not replace the quotient with an arbitrary type
or a collection of unquotiented vectors.

## Symmetry covariance

`KreinProjectiveBoundaryMap.map_mem_iff` proves preservation of boundary
membership by Mathlib's induced projective map of a linear equivalence,
assuming:

- the equivalence commutes with the complement `H`;
- its quadratic pairing scales by a nonzero real constant.

The scale may be negative, so this includes anti-isometries rather than only
positive conformal scalings. `map_mem_iff_of_commutes_operator` weakens the
first supplied condition to commutation with the original operator `L`:
commutation with its Drazin inverse and complement is then derived using the
existing Drazin commutant theorem. No projector covariance is assumed as a
replacement for that derivation.

This is preservation under explicitly supplied compatible linear symmetries.
It is not a construction of a Lie group action, a Tomita modular state, or a
manifold/conformal compactification theorem.

## Regressions

`KreinProjectiveBoundaryTests.lean` uses the native doubled real Krein carrier
and the existing square-zero Drazin example with `H = 1`:

- `(1,1)` and `(1,-1)` represent distinct boundary rays.
- `(1,0)` represents a non-null ray and is excluded.
- `(-2,-2)` represents exactly the same projective ray as `(1,1)`.
- Projectivizing each chosen packet representative recovers its ray.
- The distinct realified `modular_j` mirror preserves boundary membership
  with quadratic scale `-1`; it is not identified with the fundamental metric
  involution.
- Negation preserves boundary membership using commutation with the original
  operator, exercising the derived complement-commutation route.

The mirror test uses commutation with `H`, not commutation with the original
nilpotent operator. These are intentionally distinct sufficient conditions.

## Verification scope

The three new production modules and `KreinProjectiveBoundaryTests.lean`
compile without warnings under Lean 4.28.0. The thirteen selected axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx` or added axioms. Mathlib's representative selection is explicitly
noncomputable; the ray carrier itself is the native quotient.

Validation uses isolated, serial Lean 4.28.0 checks and the cached Mathlib
revision described in [the Green decomposition notes](KREIN_GREEN_DECOMPOSITION.md).
The repository's pinned Lean 4.28.1 verification remains blocked by incompatible
cached Mathlib headers. No dependency metadata or pins are changed.
