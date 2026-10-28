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
witness applies to every nontrivial coefficient ring. Over fields, injectivity is
equivalent to `X ≠ 0`; its range then has native `Module.finrank` equal to 4.
The range is proved equal to `NonUnitalAlgebra.adjoin K {X,Y}`. The generators
are proved not to commute when `X ≠ 0`, in every characteristic.

For the original quartet `X+Y`, `X-Y`, `X*Y-Y*X`, `X*Y+Y*X`, linear
independence additionally requires `(2 : K) ≠ 0`. This is proved using native
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
| `representation_eq_zero_iff`, `(2 : K) ≠ 0` | `quartet_combination_eq_zero_iff` |
| coefficient uniqueness, `Fintype.linearIndependent_iff` | `quartet_linearIndependent` |

## Verification

Pending focused pinned kernel checking and exact-set axiom inspection of all
15 declarations (14 theorems and one homomorphism definition), followed by
separate independent source audit and acceptance review. The workflow rebuilds
the complete selected project import closure with fresh output files.
