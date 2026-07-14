import Mathlib
import InfoGeometry.Canonical.Drazin

/-!
# Generalized Null Space Decomposition: finite algebraic spine

Source digest:

Nicola Guglielmi, Michael L. Overton, and G. W. Stewart,
"An efficient algorithm for computing the generalized null space decomposition",
SIAM Journal on Matrix Analysis and Applications 36(1), 38--54, 2015.

The paper's formalizable finite algebraic core is:

* a zero-Jordan / generalized-null-space staircase;
* the block upper triangular form `B = [[N,L],[0,M]]`, where `N` is nilpotent
  and `M` is invertible;
* the Sylvester equation `K M - N K = L`, which removes the coupling block by
  a similarity transform; and
* the resulting Drazin inverse block formula.

This file intentionally does not formalize the floating-point QR/update
algorithm, tolerance selection, or numerical stability theorem.  Those are
external numerical certificates in `tools/`.
-/

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace GeneralizedNullSpaceDecomposition

open InfoGeometry.Canonical

abbrev Mat2 (R : Type*) := Matrix (Fin 2) (Fin 2) R
abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R
abbrev Mat4 (R : Type*) := Matrix (Fin 4) (Fin 4) R

section RingBlock

variable {R : Type*} [Ring R]

/-- Paper Appendix A block: `B = [[N,L],[0,M]]`. -/
def gnsdUpper2 (N L M : R) : Mat2 R :=
  !![N, L; 0, M]

/-- Block diagonal `diag(N,M)`. -/
def gnsdDiag2 (N M : R) : Mat2 R :=
  !![N, 0; 0, M]

/-- Similarity matrix `[[1,K],[0,1]]`. -/
def gnsdShear (K : R) : Mat2 R :=
  !![1, K; 0, 1]

/-- Inverse similarity matrix `[[1,-K],[0,1]]`. -/
def gnsdShearInv (K : R) : Mat2 R :=
  !![1, -K; 0, 1]

/-- Appendix A Drazin block formula for the square-zero nilpotent case. -/
def gnsdDrazin2 (K MI : R) : Mat2 R :=
  !![0, K * MI; 0, MI]

/-- The two shear matrices are inverse. -/
theorem gnsdShear_mul_inv (K : R) :
    gnsdShear K * gnsdShearInv K = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gnsdShear, gnsdShearInv, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two shear matrices are inverse. -/
theorem gnsdShear_inv_mul (K : R) :
    gnsdShearInv K * gnsdShear K = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gnsdShear, gnsdShearInv, Matrix.mul_apply, Fin.sum_univ_two]

/--
The Sylvester equation `K M - N K = L` removes the coupling block in the GNSD
upper triangular form.
-/
theorem sylvester_similarity_zeroes_coupling
    {N L M K : R}
    (hSylv : K * M - N * K = L) :
    gnsdShearInv K * gnsdUpper2 N L M * gnsdShear K =
      gnsdDiag2 N M := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gnsdShearInv, gnsdUpper2, gnsdShear, gnsdDiag2,
      Matrix.mul_apply, Fin.sum_univ_two, ← hSylv] <;> noncomm_ring

/--
If `N² = 0`, `M` is invertible with inverse `MI`, and `K` solves
`K M - N K = L`, then the Appendix A block formula is a Drazin inverse at
index `2`.
-/
theorem gnsdDrazin2_isDrazinInverse
    {N L M K MI : R}
    (hN2 : N * N = 0)
    (hMI_left : MI * M = 1)
    (hMI_right : M * MI = 1)
    (hSylv : K * M - N * K = L) :
    Drazin.IsDrazinInverse
      (gnsdUpper2 N L M) (gnsdDrazin2 K MI) 2 := by
  refine Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gnsdUpper2, gnsdDrazin2, Matrix.mul_apply, Fin.sum_univ_two,
        ← hSylv, hMI_left, hMI_right, hN2] <;> noncomm_ring [hN2, hMI_left, hMI_right]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gnsdUpper2, gnsdDrazin2, Matrix.mul_apply, Fin.sum_univ_two,
        ← hSylv, hMI_left, hMI_right, hN2] <;> noncomm_ring [hN2, hMI_left, hMI_right]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gnsdUpper2, gnsdDrazin2, Matrix.mul_apply, Fin.sum_univ_two,
        pow_succ, ← hSylv, hMI_left, hMI_right, hN2] <;>
        noncomm_ring [hN2, hMI_left, hMI_right]

end RingBlock

section RationalJordan

/-! ## Strict finite Jordan/GNSD readout over `ℚ` -/

/-- Nilpotent shift `J₃(0)`. -/
def J3Zero : Mat3 ℚ :=
  !![0, 1, 0;
     0, 0, 1;
     0, 0, 0]

/-- The order-three zero Jordan block is nilpotent at power three. -/
theorem J3Zero_cube_eq_zero :
    J3Zero ^ 3 = 0 := by
  native_decide

/-- But `J₃(0)²` is not the zero matrix, so the nilpotence index is exactly `3`. -/
theorem J3Zero_sq_ne_zero :
    J3Zero ^ 2 ≠ 0 := by
  native_decide

/--
For zero Jordan block sizes `[3,2,1]`, the GNSD diagonal sizes are the counts
of blocks with size at least `j`: `μ₁ = 3`, `μ₂ = 2`, `μ₃ = 1`.
-/
def exampleZeroJordanSizes : List ℕ := [3, 2, 1]

def countBlocksGE (j : ℕ) (sizes : List ℕ) : ℕ :=
  (sizes.filter (fun k => j ≤ k)).length

def countBlocksExact (j : ℕ) (sizes : List ℕ) : ℕ :=
  (sizes.filter (fun k => k = j)).length

@[simp] theorem countBlocksGE_example_one :
    countBlocksGE 1 exampleZeroJordanSizes = 3 := by
  native_decide

@[simp] theorem countBlocksGE_example_two :
    countBlocksGE 2 exampleZeroJordanSizes = 2 := by
  native_decide

@[simp] theorem countBlocksGE_example_three :
    countBlocksGE 3 exampleZeroJordanSizes = 1 := by
  native_decide

@[simp] theorem countBlocksExact_example_one :
    countBlocksExact 1 exampleZeroJordanSizes = 1 := by
  native_decide

@[simp] theorem countBlocksExact_example_two :
    countBlocksExact 2 exampleZeroJordanSizes = 1 := by
  native_decide

@[simp] theorem countBlocksExact_example_three :
    countBlocksExact 3 exampleZeroJordanSizes = 1 := by
  native_decide

/-- In the `[3,2,1]` example, `μ₁ - μ₂` recovers the number of size-one blocks. -/
theorem exactSizeOne_example_eq_mu_sub :
    countBlocksExact 1 exampleZeroJordanSizes =
      countBlocksGE 1 exampleZeroJordanSizes - countBlocksGE 2 exampleZeroJordanSizes := by
  native_decide

/-- In the `[3,2,1]` example, `μ₂ - μ₃` recovers the number of size-two blocks. -/
theorem exactSizeTwo_example_eq_mu_sub :
    countBlocksExact 2 exampleZeroJordanSizes =
      countBlocksGE 2 exampleZeroJordanSizes - countBlocksGE 3 exampleZeroJordanSizes := by
  native_decide

/-- In the `[3,2,1]` example, `μ₃ - μ₄` recovers the number of size-three blocks. -/
theorem exactSizeThree_example_eq_mu_sub :
    countBlocksExact 3 exampleZeroJordanSizes =
      countBlocksGE 3 exampleZeroJordanSizes - countBlocksGE 4 exampleZeroJordanSizes := by
  native_decide

end RationalJordan

end GeneralizedNullSpaceDecomposition
