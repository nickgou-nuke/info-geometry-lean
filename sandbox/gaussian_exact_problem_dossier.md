# Gaussian elimination: exact mathematical problem and evidence dossier

Status: explicit problem specification; no unresolved premise is promoted as a theorem.

## 1. Mathematical objects and givens

Let `m n : Nat` and let

```text
A : Matrix (Fin m) (Fin n) Q
```

where `Q` is the field of rational numbers.

The executable owner is:

```text
DAG.MatrixGaussJordan.gaussJordanElimFull.go
```

Its state is:

```text
(A_current, pivotRow, column, Es)
```

where `Es` is a list of `m x m` elementary matrices. The transition scans columns from left to right. When a nonzero entry exists at or below `pivotRow`, it swaps that row into `pivotRow`, scales the pivot to one, and adds multiples of the pivot row to every other row to clear the pivot column.

The returned pair is:

```text
(gaussJordanElim A).1 = final matrix
(gaussJordanElim A).2 = recursive pivot-row counter
```

The second component is now the counter produced by the algorithm; it is not defined to be `Matrix.rank A`.

## 2. Statements already proved in Lean

The following are kernel-checked in `lean/DAG/MatrixGaussJordan.lean`:

1. Every matrix recorded in the elimination list is `IsUnit`.
2. The final matrix equals the product of the recorded elementary matrices times the initial matrix.
3. The final matrix has the same `Matrix.rank` as the initial matrix.
4. The second output is definitionally the final recursive pivot-row counter.
5. `gaussJordanElim_rank_of_pivotFun` is a conditional bridge: if a separately supplied pivot-shape witness and a separately supplied counter/cardinality equality are available, then the counter equals `Matrix.rank A`.

The last item is not an algorithm correctness theorem. Its two premises are obligations, not established facts.

## 3. Exact target theorem

The intended unconditional theorem is:

```lean
∀ {m n : Nat} (A : Matrix (Fin m) (Fin n) ℚ),
  (gaussJordanElim A).2 = Matrix.rank A
```

A sufficient constructive route is to prove, for the actual returned matrix `R := (gaussJordanElim A).1`, a function `f : Nat -> Nat` such that:

```lean
AFPGaussJordan.PivotFun R f n
```

and then prove:

```lean
(Finset.filter
  (fun i : Nat => i < m ∧ f i < n)
  (Finset.range m)).card = (gaussJordanElim A).2
```

These are not allowed to remain hidden as hypotheses in the final theorem.

## 4. Required induction invariant

For every recursive call

```text
go A_current p c Es
```

the proof must establish all of the following, with explicit bounds:

1. `0 ≤ p ≤ m` and `0 ≤ c ≤ n`.
2. The rows before `p` are already pivot rows.
3. Their pivot columns are strictly increasing and lie before `c`.
4. Each earlier pivot column is one at its pivot row and zero at every other row.
5. Every entry left of the active column in every processed row is zero except the pivot one.
6. The recorded matrix product relates `A_current` to the original matrix.
7. The counter `p` equals the number of established pivots.
8. If the current column has no admissible nonzero entry, advancing `c` preserves all seven facts.
9. If a pivot exists, swap/scale/eliminate preserves all earlier facts and adds exactly one new pivot.
10. At termination `c = n`, the resulting `f` satisfies the exact live six-field `PivotFun` definition.

The critical nontrivial obligations are preservation of earlier pivot columns when clearing a later column, and the relationship between the algorithmic counter and the `f` cardinality.

## 5. Source audit results

### Strong local source

`lean/DAG/FunctionalGaussJordan.lean`

- elementary row-operation matrices;
- inverse/`IsUnit` proofs;
- rank preservation under invertible left multiplication.

`lean/DAG/MatrixGaussJordan.lean`

- executable elimination recursion;
- recorded elementary transformations;
- invertibility and rank-preservation proofs.

### Conditional source

`lean/DAG/AFPGaussJordan.lean`

- live six-field `PivotFun` predicate;
- rank equals pivot-cardinality theorem under `PivotFun`.

This theorem proves consequences of a pivot shape. It does not prove that the executable algorithm produces that shape.

### Rejected recovery candidates

`lean_sandbox/GaussianEliminationFix.lean`

- contains five `sorry` commands in the exact induction and rank-normal-form obligations;
- comments describe the intended proof but are not proof terms.

`lean_sandbox/HarmonicKMSBridge.lean`

- uses `native_decide` for universally quantified general rank correspondence claims;
- this is not evidence of a general Gaussian-elimination proof and is not an authority source.

`lean/DAG/GaussianElimination.lean` historical corridor

- mixed generic and finite index domains;
- stale/incoherent induction branch;
- now quarantined from the production surface.

## 6. Mathlib/source literature search result

The installed mathlib source contains matrix rank, linear-map range, span, basis, and finite-dimensionality lemmas, but no general executable RREF/Gaussian-elimination algorithm matching the repository's `gaussJordanElimFull.go` state.

The repository contains no vendored Isabelle/AFP Gauss-Jordan proof source. Network search during this audit did not retrieve a proof-bearing AFP source that can be safely ported. Therefore no external theorem has been silently treated as a Lean proof.

## 7. Acceptance criteria for the next implementation

A general rank theorem may be promoted only when:

1. the exact recursive invariant is stated in Lean;
2. each no-pivot, pivot, and termination branch compiles;
3. the returned `f` and pivot counter are constructed by the algorithm, not supplied by a caller;
4. the final `PivotFun` fields are proved natively;
5. the counter/cardinality equality is proved natively;
6. `lake env lean lean/DAG/MatrixGaussJordan.lean` and `lake build DAG.GaussianElimination` both pass;
7. no `sorry`, `admit`, axiom, `native_decide` generality shortcut, or vacuous witness is used.

Until then, the theorem status is: rank preservation proved; algorithmic pivot-count equals rank open.
