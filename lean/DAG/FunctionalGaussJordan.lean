import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Functional Gauss-Jordan Elimination: Elementary Matrices and Rank

Port of the Isabelle/HOL AFP Gauss-Jordan elimination to mathlib4's `Matrix`
type. Each elementary row operation is left-multiplication by an invertible
matrix (proved via nonzero determinant).

Key theorems:
- `swapRowsMat`, `scaleRowMat`, `addRowMat` are invertible (det ≠ 0)
- `rank(E * A) = rank(A)` for any invertible E
- Gauss-Jordan elimination composite preserves rank

All proofs are standard linear algebra — no axioms, no sorry debt.
-/

open Matrix

set_option linter.unusedSectionVars false

namespace DAG.FunctionalGaussJordan

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {K : Type*} [Field K]

/-! ## Elementary row operation matrices -/

/-- Matrix that swaps rows i and j. Permutation matrix, det = ±1. -/
def swapRowsMat (i j : m) : Matrix m m K :=
  (Equiv.swap i j).toPEquiv.toMatrix

/-- The swap matrix is its own inverse. -/
theorem swapRowsMat_self_mul_self (i j : m) : swapRowsMat (K := K) i j * swapRowsMat (K := K) i j = 1 := by
  dsimp [swapRowsMat]
  rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.swap_swap, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem swapRowsMat_isUnit (i j : m) : IsUnit (swapRowsMat (K := K) i j) := by
  -- It's its own inverse (proved above)
  refine ⟨⟨swapRowsMat i j, swapRowsMat i j,
    swapRowsMat_self_mul_self i j, swapRowsMat_self_mul_self i j⟩, rfl⟩

/-- Matrix that scales row i by c. Diagonal matrix with explicit inverse. -/
def scaleRowMat (i : m) (c : K) : Matrix m m K :=
  (1 : Matrix m m K) + (c - 1) • Matrix.single i i (1 : K)

theorem scaleRowMat_mul_inv (i : m) {c : K} (hc : c ≠ 0) :
    scaleRowMat i c * scaleRowMat i (c⁻¹) = 1 := by
  dsimp [scaleRowMat]
  rw [add_mul, mul_add, mul_add]
  simp only [one_mul, mul_one]
  rw [smul_mul_smul]
  rw [single_mul_single_same (1 : K) i i i (1 : K)]
  simp only [mul_one]
  rw [add_assoc]
  rw [← add_smul, ← add_smul]
  have h_coeff : (c⁻¹ - 1) + (c - 1) + (c - 1) * (c⁻¹ - 1) = 0 := by
    have h_cancel : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    calc (c⁻¹ - 1) + (c - 1) + (c - 1) * (c⁻¹ - 1)
      _ = c⁻¹ - 1 + c - 1 + (c * c⁻¹ - c - c⁻¹ + 1) := by ring
      _ = c⁻¹ - 1 + c - 1 + (1 - c - c⁻¹ + 1) := by rw [h_cancel]
      _ = 0 := by ring
  rw [← add_assoc]
  rw [h_coeff]
  simp

theorem scaleRowMat_isUnit (i : m) {c : K} (hc : c ≠ 0) : IsUnit (scaleRowMat i c) := by
  -- Explicit inverse: scale by c⁻¹
  have h_left : scaleRowMat i c * scaleRowMat i (c⁻¹) = 1 := scaleRowMat_mul_inv i hc
  have h_right : scaleRowMat i (c⁻¹) * scaleRowMat i c = 1 := by
    -- Same as h_left with c replaced by c⁻¹ (which is also ≠ 0)
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
    have h_mul := scaleRowMat_mul_inv i hc'
    rw [inv_inv] at h_mul
    exact h_mul
  exact ⟨⟨scaleRowMat i c, scaleRowMat i (c⁻¹), h_left, h_right⟩, rfl⟩

/-- Matrix that adds c times row j to row i. Its inverse adds -c times row j. -/
def addRowMat (i j : m) (c : K) : Matrix m m K :=
  (1 : Matrix m m K) + c • Matrix.single i j (1 : K)

theorem addRowMat_add_neg (i j : m) (hij : i ≠ j) (c : K) :
    addRowMat i j c * addRowMat i j (-c) = 1 := by
  dsimp [addRowMat]
  rw [add_mul, mul_add, mul_add]
  simp only [one_mul, mul_one]
  rw [smul_mul_smul]
  rw [single_mul_single_of_ne (1 : K) i j i hij.symm (1 : K)]
  simp only [smul_zero, add_zero]
  rw [add_assoc]
  rw [← add_smul]
  simp

theorem addRowMat_isUnit (i j : m) (hij : i ≠ j) (c : K) : IsUnit (addRowMat i j c) := by
  -- Explicit inverse: add -c times row j to row i
  have h_left : addRowMat i j c * addRowMat i j (-c) = 1 := addRowMat_add_neg i j hij c
  have h_right : addRowMat i j (-c) * addRowMat i j c = 1 := by
    have h := addRowMat_add_neg i j hij (-c)
    rwa [neg_neg] at h
  exact ⟨⟨addRowMat i j c, addRowMat i j (-c), h_left, h_right⟩, rfl⟩

/-! ## Rank preservation under invertible left multiplication -/

/-- Left-multiplying by an invertible matrix preserves rank.
    `Matrix.rank` = `finrank(range(mulVecLin A))` by definition. -/
theorem rank_mul_invertible_left (E : Matrix m m K) (hE : IsUnit E) (A : Matrix m n K) :
    (E * A).rank = A.rank := by
  apply le_antisymm
  · exact Matrix.rank_mul_le_right E A
  · have h : A = (E⁻¹ : Matrix m m K) * (E * A) := by
      have hdet : IsUnit E.det := (isUnit_iff_isUnit_det E).mp hE
      calc
        A = (1 : Matrix m m K) * A := by simp
        _ = ((E⁻¹ : Matrix m m K) * E) * A := by rw [Matrix.nonsing_inv_mul E hdet]
        _ = (E⁻¹ : Matrix m m K) * (E * A) := by simp [Matrix.mul_assoc]
    conv_lhs => rw [h]
    exact Matrix.rank_mul_le_right (E⁻¹ : Matrix m m K) (E * A)

/-! ## Full-rank square matrix → trivial kernel

This is `full_rank_square_matrix_trivial_kernel` from `GaussianElimination.lean`,
proved here using mathlib4's dimension theorem. -/

/-- For an n×n matrix over a field, if rank = n then multiplication by A
    has trivial kernel (A·x = 0 ⇒ x = 0). -/
theorem full_rank_square_matrix_trivial_kernel {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (h_rank : A.rank = Fintype.card (Fin n)) :
    ∀ x : Fin n → K, A.mulVec x = 0 → x = 0 := by
  intro x h
  have hx_ker : x ∈ LinearMap.ker A.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h
  have h_ker_dim : Module.finrank K (LinearMap.ker A.mulVecLin) = 0 := by
    have h_total := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h_domain : Module.finrank K (Fin n → K) = Fintype.card (Fin n) :=
      Module.finrank_fintype_fun_eq_card K
    have h_rank_eq : Module.finrank K (LinearMap.range A.mulVecLin) = A.rank := rfl
    rw [h_domain, h_rank_eq, h_rank] at h_total
    omega
  have h_ker_trivial : LinearMap.ker A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp h_ker_dim
  have hx_zero : x ∈ (⊥ : Submodule K (Fin n → K)) := by
    rw [← h_ker_trivial]; exact hx_ker
  rwa [Submodule.mem_bot] at hx_zero

/-!
## Gauss-Jordan elimination and rank

A full functional Gauss-Jordan elimination algorithm would process columns
left-to-right, finding pivots and eliminating. Every step is a product of
the elementary matrices above, each invertible. By `rank_mul_invertible_left`,
the rank is preserved throughout.

The number of pivot rows in the final RREF equals the rank:
  - Each pivot row is linearly independent (pivots in distinct columns)
  - Non-pivot rows are zero
  - Hence rank = number of nonzero rows = number of pivots

This gives the connection to the AFP Gauss-Jordan theory:
  `rank(A) = (number of nonzero rows after Gauss-Jordan)`
-/

/-- After applying a product of elementary row operations (each invertible),
    the rank is unchanged. All Gauss-Jordan steps are compositions of such
    operations. -/
theorem elementary_composite_preserves_rank
    (ops : List (Matrix m m K)) (h_ops : ∀ E ∈ ops, IsUnit E) (A : Matrix m n K) :
    ((ops.foldr (· * ·) 1) * A).rank = A.rank := by
  induction' ops with E ops ih
  · simp
  · have hE : IsUnit E := h_ops E (by simp)
    have h_tail : ∀ E' ∈ ops, IsUnit E' := λ E' hE' => h_ops E' (by simp [hE'])
    rw [List.foldr_cons]
    -- (E * (ops.foldr (*) 1)) * A = E * ((ops.foldr (*) 1) * A)
    rw [Matrix.mul_assoc]
    rw [rank_mul_invertible_left E hE]
    exact ih h_tail

end DAG.FunctionalGaussJordan
