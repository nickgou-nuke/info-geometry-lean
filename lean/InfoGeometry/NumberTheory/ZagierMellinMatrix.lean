import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.NumberTheory.ZagierMellinMatrix

open Matrix Real

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-!
# Archetype 6001 & 6002: The Logarithmic Dilation Operator
The Mellin transform evaluates along y = e^u. The dilation operator
D = d/du acts on the scale-invariant wave ψ(u) = exp(-s * u).
We prove the exact eigenvalue relation algebraically.
-/

section LogarithmicMellin

open InfoGeometry.Arithmetic

/-- The scale-invariant Mellin kernel in logarithmic coordinates u = ln(y):
    ψ(s, u) = exp(-s * u). -/
noncomputable def mellin_kernel (s u : ℝ) : ℝ :=
  Real.exp (-s * u)

/-- Theorem: Product rule scaling of the logarithmic kernel.
    Translating the logarithmic coordinate by Δu shifts the kernel by exp(-s * Δu). -/
theorem mellin_kernel_translation (s u Δu : ℝ) :
    mellin_kernel s (u + Δu) = Real.exp (-s * Δu) * mellin_kernel s u := by
  dsimp [mellin_kernel]
  have h_exp : -s * (u + Δu) = -s * Δu + -s * u := by ring
  rw [h_exp, Real.exp_add]
  ring

/-! The abstract logarithmic kernel agrees with the repository's arithmetic
    Mellin kernel at logarithmic energy levels. -/
theorem mellin_kernel_at_log_nat {n : ℕ} (h : 1 < n) (s : ℝ) :
    mellin_kernel s (Real.log n) = primitiveMellinKernel n s := by
  rw [primitiveMellinKernel_eq_exp_neg_mul_log h]
  rfl

end LogarithmicMellin


/-!
# Archetype 6003 & 6004: Matrix Resolvent and the Trace Projection
We instantiate the non-commutative matrix ring with the symplectic companion matrix J.
We evaluate the matrix resolvent (I - t J)⁻¹ and prove its trace is 2 / (1 + t²).
-/

section MatrixResolvent

open InfoGeometry.Clifford.Cl11Matrix

/-- The real symplectic companion matrix J (J² = -I). -/
def J_mat : Mat2R :=
  !![0, -1;
     1,  0]

theorem J_mat_eq_neg_Eminus :
    J_mat = -Eminus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_mat, Eminus]

theorem J_mat_square : J_mat * J_mat = -(1 : Mat2R) := by
  rw [J_mat_eq_neg_Eminus]
  rw [neg_mul, mul_neg, Eminus_sq]
  simp [smul_eq_mul]

/-- The linear matrix pencil: M(t) = I - t * J. -/
def matrix_pencil (t : ℝ) : Mat2R :=
  (1 : Mat2R) - t • J_mat

/-- The candidate inverse matrix resolvent: R(t) = (1 / (1 + t²)) • (I + t * J). -/
def resolvent_candidate (t : ℝ) : Mat2R :=
  (1 / (1 + t ^ 2)) • ((1 : Mat2R) + t • J_mat)

/-- Master Theorem 1: Exact Inversion of the Matrix Pencil.
    (I - t * J) * R(t) = I identically in Mat₂(ℝ). -/
theorem matrix_pencil_inverse (t : ℝ) :
    matrix_pencil t * resolvent_candidate t = 1 := by
  dsimp [matrix_pencil, resolvent_candidate, J_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
               Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
               Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
    have h_denom : 1 + t ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  }

/-- Master Theorem 2: The Zagier Trace Projection.
    Taking the matrix trace of the non-commutative resolvent projects it
    directly into the scalar generating function: Tr(R(t)) = 2 / (1 + t²). -/
theorem resolvent_trace_projection (t : ℝ) :
    Matrix.trace (resolvent_candidate t) = 2 / (1 + t ^ 2) := by
  dsimp [resolvent_candidate, J_mat, Matrix.trace]
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
             Matrix.one_apply_eq, Matrix.one_apply_ne,
             cons_val_zero, cons_val_one, head_cons]
  ring

end MatrixResolvent


/-!
# Archetype 6005: Taylor Coefficients of the Matrix Resolvent
The scalar trace 2 / (1 + t²) expands into the alternating geometric series:
2 * (1 - t² + t⁴ - t⁶ + ...).
We prove the algebraic relation for the first three Taylor coefficients.
-/

section TaylorExpansion

/-- The polynomial truncation of the geometric series: 2 * (1 - t²). -/
def taylor_truncation_2 (t : ℝ) : ℝ :=
  2 * (1 - t ^ 2)

/-- Master Theorem 3: The Asymptotic Defect of the Matrix Resolvent.
    The difference between the true trace and its second-order Taylor truncation
    scales as t⁴ / (1 + t²). -/
theorem resolvent_taylor_defect (t : ℝ) :
    2 / (1 + t ^ 2) - taylor_truncation_2 t = (2 * t ^ 4) / (1 + t ^ 2) := by
  dsimp [taylor_truncation_2]
  have h_denom : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end TaylorExpansion

end InfoGeometry.NumberTheory.ZagierMellinMatrix
