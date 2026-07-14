# Gaussian source audit ledger

Status: source-only audit; no owner integration authorized by this artifact.
Date: 2026-07-11

## Exact source candidates found

| Path | Source status | Evidence from code | Classification |
|---|---|---|---|
| `lean/DAG/FunctionalGaussJordan.lean` | Direct source check succeeds | Defines `swapRowsMat`, `scaleRowMat`, `addRowMat`, `*_isUnit`, `rank_mul_invertible_left`, and `elementary_composite_preserves_rank` | Strongest live reusable kernel |
| `lean/DAG/MatrixGaussJordan.lean` | Direct source check succeeds after removing a tautological rank field | Defines the executable recursive elimination state, records elementary matrices, proves all recorded operations invertible, proves the output matrix is the invertible composite applied to `A`, and proves rank preservation | Canonical executable elimination owner; pivot-count = rank theorem remains genuinely open |
| `lean/DAG/AFPGaussJordan.lean` | Direct source check succeeds with warnings | Live `PivotFun` at lines 24-32 is an existential six-field predicate; `rank_rref_eq_pivot_count` is present at lines 286-296 | Live API, but its provenance is a working-tree mutation and must be audited separately |
| `lean/DAG/GaussianElimination.lean` | Direct source check fails | The live file declares `columns_induction_produces_pivot_fun` but compilation fails in its induction/pivot branch and has a forward reference from `gaussianRank_eq_matrix_rank` | Broken owner candidate; not a verified implementation |
| `lean_sandbox/GaussianEliminationFix.lean` | Direct source contains five `sorry` commands | `exists_rank_normal_form` has unresolved row-product, restricted-column, and final rank bridges | Incomplete proof sketch; not a recovery authority |

## Working-tree versus HEAD source facts

- `HEAD` `lean/DAG/AFPGaussJordan.lean` has a five-field `PivotFun` definition and does not compile when checked from the extracted source snapshot.
- The live working-tree `lean/DAG/AFPGaussJordan.lean` has a six-field `PivotFun` definition and does compile directly.
- `HEAD` `lean/DAG/GaussianElimination.lean` has 439 lines and fails direct checking in the old mixed-type induction/rank corridor.
- The live working-tree `lean/DAG/GaussianElimination.lean` has 650 lines and also fails direct checking in the induction/rank corridor.
- Both owner files are modified in the working tree; therefore neither the live mutation nor `HEAD` alone can be treated as a clean canonical restoration without a provenance comparison.

## Direct compiler observations

Commands run from repository root:

```text
lake env lean lean/DAG/FunctionalGaussJordan.lean
```

Result: exit 0; only dependency-manifest/local-package warnings.

```text
lake env lean lean/DAG/AFPGaussJordan.lean
```

Result: exit 0; only linter warnings.

```text
lake env lean lean/DAG/GaussianElimination.lean
```

Result: exit 1; failures remain in the induction/rank region.

## Mathematical owner boundary visible in source

The only directly checked local rank machinery is elementary-matrix rank preservation in `FunctionalGaussJordan.lean`. The source does not contain a directly checked, complete construction that:

1. recursively computes an RREF/row-echelon form for arbitrary finite rational matrices;
2. proves the resulting pivot/nonzero-row count equals `Matrix.rank`;
3. exports a complete Gaussian rank algorithm as a verified executable definition.

The `PivotFun` rank lemmas in the live `AFPGaussJordan.lean` establish consequences under an already supplied `PivotFun` hypothesis. The missing source-level construction is the theorem that produces that predicate from arbitrary `A`; the current `GaussianElimination.lean` attempt does not compile, and the sandbox attempt contains `sorry` at the corresponding obligations.

## Safe next action

Do not patch the current induction body from comments or theorem names. First locate an exact proof-bearing archive/diff/transcript containing the missing construction, or isolate a new theorem task whose statement is derived from the currently compiling `FunctionalGaussJordan` and live six-field `PivotFun` declarations. Any candidate must be checked directly with the current Lean toolchain before integration.
