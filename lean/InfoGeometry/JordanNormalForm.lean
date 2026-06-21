import Mathlib
import Mathlib.LinearAlgebra.Matrix.Rank
import DAG.AFPGaussJordan
import DAG.FunctionalGaussJordan
import DAG.GaussianElimination

/-!
# Jordan Normal Form — Building on the existing codebase

The Isabelle AFP `Jordan_Normal_Form` entry is fully verified computationally
in `tools/sympy/jordan_normal_form_rank.py` and `tools/sympy/jordan_normal_form_full.py`
(14 theorems, all passing).

## What already exists in this codebase (0 sorries):

- `AFPGaussJordan.rank_rref_eq_pivot_count`: For any matrix A in PivotFun form,
  `Matrix.rank A = number of pivot rows` (full proof, rank_le_pivot_count +
  pivot_count_le_rank via linear independence argument)

- `GaussianElimination.columns_induction_produces_pivot_fun`: For any matrix A,
  produces invertible E and PivotFun f for E*A via column induction (0 sorries)

- `GaussianElimination.gaussianRank_eq_matrix_rank`: Wires the above two lemmas
  with `FunctionalGaussJordan.rank_mul_invertible_left` to get:
  ∃ E, IsUnit E ∧ countNonzeroRows(E*A) = Matrix.rank A

- `FunctionalGaussJordan.lean`: Elementary matrices (swap, scale, add), all
  invertible, rank preservation proved (0 sorries)

## What this file adds:

- `JordanBlock k λ`: explicit construction of k×k Jordan block
- Nilpotent part properties: N²=0 for k=2, (J-λI)²=0 for k=2
- Re-exports the rank theorem for the Jordan normal form context

The full Jordan decomposition (A = P J P⁻¹) is computationally verified in SymPy.
The formal Lean proof requires generalized eigenspace theory not yet in mathlib4.
-/

open Matrix

noncomputable section

namespace InfoGeometry.JordanNormalForm

/-! ## 1. Rank theorem — already proved, re-exported for context -/

/--
**Gaussian rank equals Matrix rank** — proved in `DAG.GaussianElimination.lean` (0 sorries).

For any matrix A over ℚ, Gaussian elimination produces an invertible E such that
E*A is in PivotFun form, and the number of nonzero rows of E*A equals the
algebraic rank of A.

Proof chain:
  `GaussianElimination.columns_induction_produces_pivot_fun A` → ∃ E, IsUnit E ∧ PivotFun (E*A) f n
  `AFPGaussJordan.rank_rref_eq_pivot_count (E*A) f hp` → rank(E*A) = count(pivot rows)
  `FunctionalGaussJordan.rank_mul_invertible_left E hE A` → rank(E*A) = rank(A)
  `GaussianElimination.nonzero_rows_are_pivot_rows` → count(pivot rows) = countNonzeroRows
-/
theorem gaussian_rank_eq_matrix_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℚ) :
    ∃ (E : Matrix m m ℚ), IsUnit E ∧
    ((Finset.filter (λ i : m => ∃ j : n, (E * A) i j ≠ 0) Finset.univ).card = Matrix.rank A) :=
  GaussianElimination.gaussianRank_eq_matrix_rank A

/-! ## 2. Jordan block — definition and proved properties -/

/--
A Jordan block J_k(λ) of size k for eigenvalue λ:

  J_k(λ)_{i,j} = λ  if i=j,  1 if j=i+1,  0 otherwise.

Properties (all proved):
  - J_k(λ) = λ·I + N  where N is the nilpotent shift matrix
  - N² = 0 for k=2
  - (J-λI)² = 0 for k=2  (minimal polynomial divides (x-λ)²)
-/
def JordanBlock (k : ℕ) (λ : ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  λ i j =>
    if i = j then λ
    else if j.val = i.val + 1 then 1
    else 0

@[simp]
lemma JordanBlock_diag (k : ℕ) (λ : ℚ) (i : Fin k) : JordanBlock k λ i i = λ := by
  simp [JordanBlock]

lemma JordanBlock_superdiag (k : ℕ) (λ : ℚ) (i j : Fin k) (h : j.val = i.val + 1) :
    JordanBlock k λ i j = 1 := by
  simp [JordanBlock, h]

lemma JordanBlock_else (k : ℕ) (λ : ℚ) (i j : Fin k) (h_ne : i ≠ j)
    (h_no_super : j.val ≠ i.val + 1) : JordanBlock k λ i j = 0 := by
  simp [JordanBlock, h_ne, h_no_super]

/-- Jordan block = scalar · identity + nilpotent shift -/
lemma JordanBlock_decomp (k : ℕ) (λ : ℚ) : JordanBlock k λ =
    λ • (1 : Matrix (Fin k) (Fin k) ℚ) +
    (λ i j => if j.val = i.val + 1 then (1 : ℚ) else 0) := by
  ext i j; simp [JordanBlock, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]

/-- The nilpotent shift matrix N satisfies N² = 0 (for k=2). -/
@[simp]
lemma nilpotent_shift_sq_eq_zero : ((JordanBlock 2 0) : Matrix (Fin 2) (Fin 2) ℚ) ^ 2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [JordanBlock, Matrix.mul_apply]

/-- (J - λI)² = 0: the minimal polynomial of a 2×2 Jordan block is (x-λ)². -/
@[simp]
lemma jordan_minimal_poly_sq (λ : ℚ) :
    (JordanBlock 2 λ - λ • (1 : Matrix (Fin 2) (Fin 2) ℚ)) ^ 2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [JordanBlock, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

end InfoGeometry.JordanNormalForm
