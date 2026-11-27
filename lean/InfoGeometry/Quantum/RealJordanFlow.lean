/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.LogJordanKreinCore
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Real square-zero exponential and the Jordan flow

The matrix exponential of a real square-zero matrix truncates exactly.  This
identifies the existing `Quantum.LogJordanKreinCore.expJordanCell` polynomial
with the native analytic exponential, gives its additive flow law and inverse,
and proves the logarithmic coefficient after the positive change of parameter
`t = log x`.

The real exponential formula also exists for the separate canonical Jordan
owner.  The reusable result here treats an arbitrary finite real square-zero
matrix and connects the quantum owner's existing definitions to that analytic
operation without importing the complex monodromy construction.

A symmetric square-zero map on a real inner product space is zero.  The
nonzero Jordan shear is therefore compatible with the existing indefinite
Krein symmetry, not a nonzero symmetric square-zero operator for a positive
inner product.  No statement about unbounded operator domains, modular
generators, Tanaka prolongation or infinite-dimensional spectral theory is
asserted.
-/

noncomputable section

namespace InfoGeometry.Quantum.RealJordanFlow

open Matrix
open LogJordanKreinCore

section SquareZero

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact truncation of the native exponential for any real square-zero matrix. -/
theorem exp_smul_of_sq_zero (A : Matrix n n ℝ) (hA : A * A = 0) (t : ℝ) :
    NormedSpace.exp (t • A) = 1 + t • A := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' k : ℕ, ((Nat.factorial k : ℕ) : ℝ)⁻¹ • (t • A) ^ k) = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, pow_zero, pow_one]
  · intro k hk
    have h2k : 2 ≤ k := Nat.not_lt.mp (by simpa only [Finset.mem_range] using hk)
    have hsq : (t • A) ^ 2 = 0 := by
      rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hA, smul_zero]
    rw [pow_eq_zero_of_le h2k hsq, smul_zero]

/-- The native exponential of a real scalar matrix is the scalar exponential. -/
theorem exp_real_smul_one (s : ℝ) :
    NormedSpace.exp (s • (1 : Matrix n n ℝ)) = Real.exp s • (1 : Matrix n n ℝ) := by
  have hs : s • (1 : Matrix n n ℝ) = Matrix.diagonal (fun _ : n => s) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hs, Matrix.exp_diagonal]
  ext i j
  by_cases h : i = j <;> simp [h, Real.exp_eq_exp_ℝ]

/-- Scalar dilation and a square-zero shear commute inside the matrix algebra. -/
theorem exp_scalar_add_sq_zero (A : Matrix n n ℝ) (hA : A * A = 0) (s t : ℝ) :
    NormedSpace.exp (s • (1 : Matrix n n ℝ) + t • A) =
      Real.exp s • (1 + t • A) := by
  have hcomm : Commute (s • (1 : Matrix n n ℝ)) (t • A) :=
    (Commute.one_left (t • A)).smul_left s
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_real_smul_one,
    exp_smul_of_sq_zero A hA]
  simp

end SquareZero

/-- The existing Jordan cell splits into its scalar and nilpotent summands. -/
theorem jordanCell_scalar_add (delta : ℝ) : L0 delta = delta • (1 : M2R) + N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L0, N]

/-- The quantum owner's existing closed formula equals the native analytic exponential. -/
theorem expJordanCell_eq_exp (t delta : ℝ) :
    expJordanCell t delta = NormedSpace.exp (t • L0 delta) := by
  rw [jordanCell_scalar_add, smul_add, smul_smul,
    exp_scalar_add_sq_zero N jordanNilpotent_sq]
  rfl

@[simp]
theorem expJordanCell_zero (delta : ℝ) : expJordanCell 0 delta = 1 := by
  simp [expJordanCell]

/-- Addition of real time parameters agrees with multiplication of evolution matrices. -/
theorem expJordanCell_add (s t delta : ℝ) :
    expJordanCell (s + t) delta = expJordanCell s delta * expJordanCell t delta := by
  rw [expJordanCell_eq_exp, expJordanCell_eq_exp, expJordanCell_eq_exp, add_smul]
  exact Matrix.exp_add_of_commute _ _
    (((Commute.refl (L0 delta)).smul_left s).smul_right t)

/-- Reversing the real time parameter gives a two-sided inverse. -/
theorem expJordanCell_mul_neg (t delta : ℝ) :
    expJordanCell t delta * expJordanCell (-t) delta = 1 := by
  rw [← expJordanCell_add, add_neg_cancel, expJordanCell_zero]

theorem expJordanCell_neg_mul (t delta : ℝ) :
    expJordanCell (-t) delta * expJordanCell t delta = 1 := by
  rw [← expJordanCell_add, neg_add_cancel, expJordanCell_zero]

/-- The flow has a native unit at every real time. -/
def expJordanCellUnit (delta t : ℝ) : M2Rˣ where
  val := expJordanCell t delta
  inv := expJordanCell (-t) delta
  val_inv := expJordanCell_mul_neg t delta
  inv_val := expJordanCell_neg_mul t delta

/-- Native one-parameter group from additive real time to invertible matrices. -/
def jordanFlowHom (delta : ℝ) : Multiplicative ℝ →* M2Rˣ where
  toFun t := expJordanCellUnit delta t.toAdd
  map_one' := by
    apply Units.ext
    exact expJordanCell_zero delta
  map_mul' s t := by
    apply Units.ext
    exact expJordanCell_add s.toAdd t.toAdd delta

/-- The positive parameter change exposes an actual logarithmic shear term. -/
theorem exp_log_smul_jordanCell (x delta : ℝ) (hx : 0 < x) :
    NormedSpace.exp (Real.log x • L0 delta) =
      x ^ delta • (1 + Real.log x • N) := by
  rw [← expJordanCell_eq_exp, expJordanCell, Real.rpow_def_of_pos hx]

/-- Ordinary trace retains only the scalar term of the logarithmic flow. -/
theorem trace_exp_log_jordanCell (x delta : ℝ) (hx : 0 < x) :
    Matrix.trace (NormedSpace.exp (Real.log x • L0 delta)) = 2 * x ^ delta := by
  rw [← expJordanCell_eq_exp, trace_exp_jordanCell, Real.rpow_def_of_pos hx]

/-- The existing transpose-shear detector reads the genuine logarithmic coefficient. -/
theorem detector_trace_exp_log_jordanCell (x delta : ℝ) (hx : 0 < x) :
    Matrix.trace (N.transpose * NormedSpace.exp (Real.log x • L0 delta)) =
      Real.log x * x ^ delta := by
  rw [← expJordanCell_eq_exp, detector_trace_jordanCell, Real.rpow_def_of_pos hx]

/-- The shear is nonzero after the positive parameter change precisely away from `x = 1`. -/
theorem logarithmic_coefficient_ne_zero (x delta : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    Real.log x * x ^ delta ≠ 0 := by
  apply mul_ne_zero
  · intro h
    apply hx1
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ = 1 := by rw [h, Real.exp_zero]
  · exact ne_of_gt (Real.rpow_pos_of_pos hx delta)

theorem logarithmic_coefficient_eq_zero_iff (x delta : ℝ) (hx : 0 < x) :
    Real.log x * x ^ delta = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_contra hx1
    exact logarithmic_coefficient_ne_zero x delta hx hx1 h
  · rintro rfl
    simp

/-- The existing Krein-symmetric Jordan cell is not an ordinary symmetric matrix. -/
theorem jordanCell_not_symm (delta : ℝ) : ¬ (L0 delta).IsSymm := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [L0, Matrix.transpose_apply] at h01

section PositiveInnerProductBoundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive definiteness rules out a nonzero symmetric square-zero linear map.
Completeness and finite dimensionality are not needed. -/
theorem symmetric_sq_zero_eq_zero (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hT2 : T * T = 0) : T = 0 := by
  ext v
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hv : T (T v) = 0 := congrArg (fun S : E →ₗ[ℝ] E => S v) hT2
  calc
    inner ℝ (T v) (T v) = inner ℝ v (T (T v)) := hT v (T v)
    _ = 0 := by rw [hv, inner_zero_right]

/-- A real symmetric operator with a square-zero scalar shift is itself scalar. -/
theorem symmetric_scalar_shift_sq_zero (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (delta : ℝ) (hshift : (T - delta • (1 : E →ₗ[ℝ] E)) *
      (T - delta • (1 : E →ₗ[ℝ] E)) = 0) : T = delta • (1 : E →ₗ[ℝ] E) := by
  apply sub_eq_zero.mp
  apply symmetric_sq_zero_eq_zero _ _ hshift
  exact hT.sub (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one)

end PositiveInnerProductBoundary

end InfoGeometry.Quantum.RealJordanFlow
