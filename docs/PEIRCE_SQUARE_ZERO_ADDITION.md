# Square-zero Moore-Penrose geometry of Drazin shell corners

## Source and theorem contract

This is an additive follow-up to PR #195, based on
`096537815fc734b462f7a69af6394af79d3c3c4b`. It consumes the two notes
`Pasted text(20261023-035916).txt` and `Pasted text (2)(20261023-040521).txt`.
The pasted source is not adopted verbatim, and its compilation claims are not
verification evidence. Neither original upload is modified.

Carrier: an arbitrary associative `Ring R`, with `StarRing R` where the native
Moore-Penrose predicate is used. Matrix rings are instances, not substitutes.
No new inverse predicate, duplicate shell definition, or Lie/Jordan carrier is
introduced. The symmetrized product is unnormalized (xy+yx).

Owners read and reused:
- `Singular.MoorePenrose.IsMoorePenroseInverse`: aba=a, bab=b, star(ab)=ab,
  star(ba)=ba.
- `Singular.MoorePenroseSectors.support_isStarProjection` and Mathlib
  `IsStarProjection.add` / `.one_sub`.
- `Canonical.Drazin.IsDrazinInverse`, its actual regular/complementary
  projectors, nilpotent part, and uniform nilpotency bound.
- `DrazinObliqueShellResolution.dressedShell`, its idempotence and cross-products.
- `DrazinShellCascade.operator_cascade` and `.shell_step_block_zero`.
- `DrazinShellMatrixAction`: the complete existing oblique matrix witness.

Additional search lanes inspected existing Peirce corner, square-zero
commutator, and Kantor owners. `SquareZeroStrainRotation` concerns a different
commutator and the pair x,star(x), not x and its arbitrary MP inverse. The
existing general Kantor infrastructure is not replaced by polynomial aliases.
No repository-wide absence or novelty claim is made.

## Explicit source corrections

1. The proposed triple formula is false. Its residual is exactly
   `(zx-xz)y`. The corrected formula is
   `xyz+zyx = (xy)z+z(xy)-z(xy-yx)`.
   A 2x2 matrix-unit counterexample to the proposed formula is kernel-tested.
2. The sum d+b for a square-zero element and its MP inverse need not be
   self-adjoint. The matrices d=[[0,2],[0,0]], b=[[0,0],[1/2,0]] satisfy all four
   Penrose laws but their sum is not self-adjoint. Its square is nevertheless
   the native star projection db+bd, and the sum is tripotent.
3. A Drazin projector commutes with its operator; it need not be central in
   the ambient matrix ring. A 2x2 Drazin witness refutes universal centrality.
4. Oblique shell idempotents are not silently upgraded to star projections.
   Corner supports have the one-sided localization stated in the second note.
   An explicit existing oblique example shows its MP inverse need not belong
   to the reverse oblique corner.
5. The second note contains a literal placeholder proof and an R/real type
   mismatch before its replacement code. This addition imports the already
   checked cascade instead of copying either definition block.
6. All power statements keep exponent zero valid. No bare N^0=0 assertion is
   introduced, and the Drazin witness exponent is not declared minimal.

## Causal proof order

Associative corner product -> square-zero corner.
Native Penrose equations + square-zero -> zero support products -> reciprocal
square-zero -> active/common-null star projections -> grading and reciprocal
sum tripotence -> opposite grading actions and anticommutation.

Existing Drazin shells -> actual inter-shell corners -> triangular double sum
-> local square-zero MP results, conditional on a supplied corner MP inverse.
The whole nilpotent operator is not required to be square-zero.

The general result also proves the converse: d^2=0 iff (bd)(db)=0 for a native
MP pair. The higher-order symmetric overlap formula is valid without a
square-zero or commuting-support hypothesis.

## Files and verification scope

- Algebra/PeirceRegularityIdentities.lean: elementary unnormalized product
  identities and exact formula defect.
- Singular/MoorePenroseSquareZero.lean: native support projections and grading.
- Canonical/DrazinShellPeirce.lean: regularity defect, corner reconstruction,
  support localization, and local graded algebra identities.
- Canonical/PeirceSquareZeroExamples.lean: matrix counterexamples and a concrete
  nontrivial corner of the existing oblique example.

Run the scoped workflow or the locked local build with these four targets.
The workflow compiles exact unchanged owner files against the pinned Mathlib
and toolchain, audits every new declaration, and packages source hashes and
logs. Success must be established by its actual result, not this document.
The check is not a full-repository or complete umbrella build.

No existence theorem for MP inverses over arbitrary star rings is asserted.
No bundled Kantor system, graded algebra, analytic Hodge/Dirac operator,
spectral eigenspace resolution, attention training change, or physical theory
is claimed by these polynomial identities. Existing owners and dependency pins
remain unchanged. The PR is not merged by this work.
