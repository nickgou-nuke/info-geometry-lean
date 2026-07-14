# AFP Gauss–Jordan proof context

Status: repository-grounded extraction from the downloaded AFP mirror.

## Authoritative source paths

- `external_refs/mirror-afp-devel/thys/Gauss_Jordan/Gauss_Jordan.thy`
- `external_refs/mirror-afp-devel/thys/Gauss_Jordan/Rref.thy`
- `external_refs/mirror-afp-devel/thys/Gauss-Jordan-Elim-Fun/Gauss_Jordan_Elim_Fun.thy`
- `external_refs/mirror-afp-devel/thys/Echelon_Form/Echelon_Form.thy`

These are actual Isabelle/HOL AFP sources in the repository, not Lean reconstructions.

## AFP algorithmic definitions

`Gauss_Jordan.thy` defines:

- `Gauss_Jordan_in_ij A i j`: choose the least row at or below `i` with a nonzero entry in column `j`; swap it into row `i`; scale the pivot to `1`; subtract multiples of the pivot row from all other rows.
- `Gauss_Jordan_column_k (i,A) k`: process column `k`; if the active column has no nonzero entry in rows at or below the active row, leave the matrix unchanged; otherwise apply `Gauss_Jordan_in_ij` and increment the active row.
- `Gauss_Jordan_upt_k A k`: fold `Gauss_Jordan_column_k` over columns `0..<Suc k`.
- `Gauss_Jordan A`: process all columns through `ncols A - 1`.

The algorithm processes columns left-to-right and maintains an active pivot row.

## AFP RREF predicate

`Rref.thy` defines:

- `is_zero_row_upt_k i k A`: row `i` is zero in columns `< k`.
- `reduced_row_echelon_form_upt_k A k`: four conditions up to column `k`:
  1. zero rows occur only below nonzero rows;
  2. the first nonzero entry of every nonzero row is `1`;
  3. first nonzero positions increase strictly down adjacent nonzero rows;
  4. every pivot column is zero in all other rows.
- `reduced_row_echelon_form A`: the up-to-`ncols` predicate.

The main introduction theorem is:

```isabelle
reduced_row_echelon_form_upt_k_intro
```

The main monotonicity theorem is:

```isabelle
rref_suc_imp_rref
```

## AFP step-preservation proof structure

The correctness proof in `Gauss_Jordan.thy` is organized around these facts:

1. `Gauss_Jordan_in_ij_1`: the new pivot entry equals `1`.
2. `Gauss_Jordan_in_ij_0`: every other entry in the new pivot column equals `0`.
3. `Gauss_Jordan_in_ij_preserves_previous_elements`: entries in columns `< k` are unchanged when processing column `k`, provided the current matrix is RREF up to `k` and the pivot is chosen below the last established nonzero row.
4. `is_zero_after_Gauss`: zero rows below the active region remain zero in processed columns.
5. `condition_1_part_1` through `condition_1_part_5`: preservation of the zero-row ordering condition through the column step, split by whether all rows are zero, whether the pivot is in row zero, whether rows below the greatest nonzero row are zero, and whether the greatest nonzero row reaches the matrix boundary.
6. `condition_1`: combines the previous cases to establish the zero-row ordering condition after a column step.
7. Additional condition lemmas establish the pivot-one, increasing-leading-position, and pivot-column-zero conditions after a column step.
8. `reduced_row_echelon_form_upt_k_Gauss_Jordan_column_k`: combines all four conditions and proves RREF-up-to-`Suc k` after processing column `k`.
9. The final theorem applies the column-step theorem over the complete column range.

## AFP functional algorithm proof

`Gauss-Jordan-Elim-Fun/Gauss_Jordan_Elim_Fun.thy` is a separate functional algorithm over `nat => nat => 'a` matrices. It defines:

```isabelle
gauss_jordan A m
```

recursively on the number of rows. Its correctness invariant is:

```isabelle
unit A m n
```

meaning columns `m..<n` have identity-column shape, together with preservation of the linear-system solution relation:

```isabelle
solution A n x
```

The core lemmas are:

- `solution_swap`
- `solution_upd1`
- `solution_upd_but1`
- `gauss_jordan_lemma`
- `gauss_jordan_correct`

The proof of `gauss_jordan_lemma` is induction on `m`, extracts the selected pivot from `dropWhile`, proves the transformed matrix retains the `unit` invariant, invokes the induction hypothesis on the smaller matrix, and transfers the solution relation back through swap/scale/elimination invariance.

## Port mapping to the current Lean owner

Current Lean executable:

```lean
DAG.MatrixGaussJordan.gaussJordanElimFull.go
```

AFP `Gauss_Jordan_column_k` corresponds to one recursive `go` step at `(pivotRow, col)`.

AFP `Gauss_Jordan_in_ij` corresponds to the current Lean composition:

```lean
swapRowsMat
scaleRowMat
eliminationMatrices
```

The current Lean owner already proves the algebraic factorization:

```lean
go_R_eq
```

and invertibility of all elementary factors:

```lean
go_all_invertible
```

The missing native RREF construction must port the AFP step invariant, not merely reuse the AFP `PivotFun` consequences. The required Lean invariant should track:

1. processed pivot rows are below the active row counter;
2. their pivot columns are strictly increasing and below the active column;
3. each processed pivot column is standard basis form;
4. all earlier processed entries are preserved by later elimination;
5. rows declared zero remain zero in processed columns;
6. the active row counter equals the number of established pivots;
7. the accumulated elementary-product factor still relates the current matrix to the original matrix.

## Authority boundary

The original AFP source supplies algorithmic proof structure and theorem shapes. It is not a Lean proof. Every ported result must be re-proved by Lean's kernel against the current `MatrixGaussJordan.go` definitions. No AFP theorem is imported as an axiom or treated as proof evidence by name alone.
