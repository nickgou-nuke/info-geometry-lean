# Faithful Peirce matrix representation

## Intake and claim boundary

This continues the supplied 2026-10-28 operator notes, especially the claim that
the square-zero/reflexive multiplication table generates a four-dimensional
algebra. Original intake hashes are preserved in the
[PR #257 contract](https://github.com/nickgou-nuke/info-geometry-lean/blob/b67208c58a877483a9476b71173c55ebef9abc4d/docs/SQUARE_ZERO_TRIPOTENT_CONTRACT.md#intake-sha256).
PR #257 proved that table and its tripotent consequences; a table
alone does not establish faithfulness or linear independence.

The ambient carrier here is `Matrix n n K`, with arbitrary finite index type
`n`. No basis change, diagonalization, entrywise multiplication, or commuting
generator hypothesis is imposed. The source of the representation is the
full noncommutative algebra `Matrix (Fin 2) (Fin 2) K`; it parametrizes actual
operators in the ambient algebra, rather than replacing them with scalars.

The existing predicate `IsDualSeedPair X Y` states exactly:
`X*X=0`, `Y*Y=0`, `X*Y*X=X`, and `Y*X*Y=Y`.
The representation preserves addition, multiplication, and scalar action:

```text
M ↦ M₀₀ • (X*Y) + M₀₁ • X + M₁₀ • Y + M₁₁ • (Y*X).
```

It is a native `NonUnitalAlgHom`, defined over commutative coefficient rings.
No commutativity of matrix multiplication is assumed; the imported source
witness applies to every nontrivial commutative coefficient ring. Over fields, injectivity is
equivalent to `X ≠ 0`; its range then has native `Module.finrank` equal to 4.
The range is proved equal to `NonUnitalAlgebra.adjoin K {X,Y}`. The generators
are proved not to commute when `X ≠ 0`, in every characteristic.

For the original quartet `X+Y`, `X-Y`, `X*Y-Y*X`, `X*Y+Y*X`, linear
independence additionally requires `(2 : R) ≠ 0`. This is proved using native
`LinearIndependent`, not a structure storing independence as a field.

The image of the identity is `H=X*Y+Y*X`. This is the identity on the supported
image; it need not be the ambient identity. The four-dimensional image need
not exhaust the whole corner `H * Matrix n n K * H`: multiplicities can make
that corner larger. No Clifford universal property, star-algebra equivalence,
spectral statement, or physical interpretation is claimed.

## Grounded owners

- `Core/DualSeedPeirce.IsDualSeedPair`: existing four-equation input and
  matrix-unit product laws.
- `Core/PeirceRotor.peirceBlock` and `peirceBlock_mul`: existing actual operator
  evaluation and multiplication law. Reused in the homomorphism construction.
- `Core/DiracSuperalgebra` and `Singular/SquareZeroChiralHodge`: existing support
  expressions; no new support or inverse predicates are introduced.
- `Core/SupercolorMatrixUnitBridge`: inspected fixed coordinate zero-extension
  embedding, distinct from arbitrary reflexive seeds.
- `Physics/ChevalleyDyadCornerMatrix`: inspected CAR matrix-unit/corner owner;
  its full-support assumptions do not replace the partial-support construction.
- `Canonical/MatrixTwoNoncommutativity`: generic closed noncommutativity
  witness for the source algebra, reused by import.
- mathlib `NonUnitalAlgHom`, `NonUnitalAlgHom.range`, `NonUnitalAlgebra.adjoin`,
  `LinearMap.ofClass`, `Matrix.single_mul_mul_single`,
  `LinearMap.finrank_range_of_inj`, `Module.finrank_matrix`, and
  `Fintype.linearIndependent_iff`: native target interfaces.

## Principal proof dependencies

These prerequisite-to-consumer edges define an acyclic declaration order;
its reflexive transitive closure is the relevant causal partial order.
They describe proof dependence, not physical time. No generated graph
freshness or automatic semantic equivalence is asserted.

| Prerequisite | Consumer |
| --- | --- |
| `peirceBlock_mul` | `representation` multiplication proof |
| `representation` | single-matrix-unit images and identity image |
| `representation_one`, native `map_mul` | left/right support action |
| single-matrix-unit images, native adjoin minimality | `range_eq_adjoin` |
| reflexivity and square-zero equations | `generators_mul_ne` |
| `Matrix.single_mul_mul_single`, `representation_single01`, `X ≠ 0` | `representation_eq_zero_iff` |
| `representation_eq_zero_iff`, native `map_sub` | `representation_injective` |
| `representation_injective`, `representation_single01` | `representation_injective_iff` |
| `representation_injective`, native dimension lemmas | `finrank_range` |
| `range_eq_adjoin`, `finrank_range` | `finrank_adjoin` |
| `representation_eq_zero_iff`, `(2 : R) ≠ 0` | `quartet_combination_eq_zero_iff` |
| coefficient uniqueness, `Fintype.linearIndependent_iff` | `quartet_linearIndependent` |

## Verification

The focused [run 40717030280](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40717030280),
[job 122917404783](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40717030280/job/122917404783),
passed on 2026-10-28. Source commit: `f9735f5439586373c87768b00a51f13c7d26b3ee`.
Checked merge: `0df3cdaf31063fd14af4be27d14af46a8be76ced`, against
base `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.

- All 23 project modules in the selected import closure rebuilt serially into
  fresh project output files using the pinned mathlib cache.
- Lean `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`;
  Lake `5.0.0-src+5045d00`; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
  Dependency source and pins are unchanged.
- Exact-set axiom audit: all 15 declarations (14 theorems and one native
  homomorphism definition) use only `propext`, `Classical.choice`, `Quot.sound`.
- No source placeholders, custom axioms, `unsafe`, or `native_decide`.
  New modules produce zero Lean warnings. Static syntax and diff checks pass.
- Existing imported owners emit 23 Lean warnings: 14 in `Singular/MoorePenrose`,
  two in `Core/JordanPeirceDecomposition`, seven in `Core/JordanAssociator`.
  These are deprecation/style/unused-argument warnings; the owners are unchanged.
- The semantic screen reports two warning-level `trivial_surface` findings on
  `representation_single01` and `representation_single10`. Both are genuine
  matrix-unit image identities, used by injectivity and generated-subalgebra
  proofs. No semantic-screen error is reported; the warnings are retained.
- Separate independent semantic source audit: PASS at the documented scope.
  Independent QA verdict: `accepted_limited_scope`, after independently
  verifying the successful job, source hashes, complete declaration inventory,
  axiom dependencies, and warning classification.

This is focused kernel acceptance, not full-repository build success. Existing
style run `40715550949` fails on the `Physics/PellisFineStructure.lean` /
`PellisfineStructure.lean` case collision. Sorry Gate run `40715552494` fails
because its build job cannot find `lake` (exit 127), before theorem checking.

The final evidence commit changes only this document; checked proof sources,
audit module, build script, workflow, and dependency pins remain unchanged.

## Verified source SHA256

- `PeirceMatrixRepresentation.lean`: `55b000ad8799a84b926a82c668f9cebb088205c0ea23c909f19e08b4d36f701b`.
- `PeirceQuartetIndependence.lean`: `1a20992533686d92e753d25e251fef27e149a8762ca0cae699bb7f94119242e1`.
- `PeirceRepresentationAudit.lean`: `67d5449c60d5e41499bb9eb13a1532b7c1bab5ead2395c2614f329bddf739a74`.
