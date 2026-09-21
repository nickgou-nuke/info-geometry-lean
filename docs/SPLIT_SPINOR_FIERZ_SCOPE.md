# Real split Clifford grades and spinor bilinears

The signature is the repository's recursive real `Qsplit`, of signature `(n,n)`.
`SplitCliffordGrades.lean` constructs a finite basis of its vector space,
the exterior-power bases, and a full Clifford basis transported through
mathlib's `CliffordAlgebra.equivExterior` linear equivalence. This equivalence
is not an algebra equivalence: exterior and Clifford multiplication differ.
Grade `k` has dimension `choose (2*n) k`; the total dimension is `2^(2*n)`.
The basis is indexed by subsets of `Fin (2*n)`, with degree their cardinality.

`SplitSpinorFierz.lean` uses the existing recursive gamma representation and
its all-stage surjectivity theorem. Equality of dimensions supplies injectivity
and a finite-stage algebra equivalence to real `2^n` by `2^n` matrices. It
transports the Clifford basis to matrices and expands every spinor dyad in
that basis. The contraction identity

```
(first * bar(second)) (third * bar(fourth))
  = (bar(second) third) (first * bar(fourth))
```

is expressed by native matrix outer products and proved coefficientwise for
every channel. The existing `SpinorBilinearSoldering.lean` owns those generic
outer-product and adjoint-support identities. Reconstruction does not assume
an unproved Clifford completeness axiom or assume the representation injective.

## Scope

- At `n=2`, grade dimensions are `1,4,6,4,1`, but the real signature is `(2,2)`,
  not Minkowski `(1,3)`.
- Coefficients are basis coordinates. An explicit trace-dual blade formula
  with signature-dependent signs is a separate result, not asserted here.
- Chiral idempotents need not be primitive. A grading decomposition is not
  a proof that the resulting left ideals are minimal.
- A full spinor dyad is rank at most one. Completeness of the ambient matrix
  basis does not make its bilinear coefficients unconstrained independent data.
- No Wigner decomposition, nuclear shape, stability, spacetime ontology,
  condensate, confinement, or mass gap follows from these algebraic identities.
- This module addresses finite stages. It adds no colimit and claims no new
  compatibility between a grade decomposition and the tower bonding maps.

## Verification

Full proof scripts and regression examples are present without placeholders.
Kernel verification is pending the shared build lane, not certified complete.

```
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.CliffordWeyl.SplitSpinorFierzTests
```
