/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Residual estimates for real skew operators on an explicit domain

A skew-symmetric linear map `K : D →ₗ[ℝ] H` is orthogonal to its argument.
Subtracting a clock term `b • J v` preserves that orthogonality when
`inner ℝ v (J v) = 0`. Pythagoras then splits the residual of a real mode into
its orthogonal part and the square of its real growth parameter.

The domain is an existing `Submodule ℝ H`. Neither boundedness, completeness,
density, a self-adjoint extension, nor an arithmetic spectral realization is
needed for these pointwise conclusions. The clock need only satisfy the stated
orthogonality condition at the chosen vector.
-/

namespace InfoGeometry.OperatorAlgebra.RealSkewDomainResidual

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Submodule ℝ H}

/-- Skew symmetry on the actual domain implies pointwise orthogonality. -/
theorem inner_self_apply_eq_zero (K : D →ₗ[ℝ] H)
    (hK : ∀ u v : D, inner ℝ (u : H) (K v) + inner ℝ (K u) (v : H) = 0)
    (v : D) : inner ℝ (v : H) (K v) = 0 := by
  have h := hK v v
  rw [real_inner_comm (v : H) (K v)] at h
  linarith

/-- An orthogonal clock term does not change the vanishing radial pairing. -/
theorem inner_clock_residual_eq_zero (K : D →ₗ[ℝ] H)
    (hK : ∀ u v : D, inner ℝ (u : H) (K v) + inner ℝ (K u) (v : H) = 0)
    (J : H →ₗ[ℝ] H) (v : D) (b : ℝ)
    (hJ : inner ℝ (v : H) (J (v : H)) = 0) :
    inner ℝ (v : H) (K v - b • J (v : H)) = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_apply_eq_zero K hK v, hJ]
  simp

/-- Exact real Pythagorean splitting of the domain-level mode residual. -/
theorem residual_norm_sq (K : D →ₗ[ℝ] H)
    (hK : ∀ u v : D, inner ℝ (u : H) (K v) + inner ℝ (K u) (v : H) = 0)
    (J : H →ₗ[ℝ] H) (v : D) (a b : ℝ)
    (hJ : inner ℝ (v : H) (J (v : H)) = 0) :
    ‖K v - b • J (v : H) - a • (v : H)‖ ^ 2 =
      ‖K v - b • J (v : H)‖ ^ 2 + a ^ 2 * ‖(v : H)‖ ^ 2 := by
  have horth : inner ℝ (K v - b • J (v : H)) (v : H) = 0 := by
    rw [real_inner_comm]
    exact inner_clock_residual_eq_zero K hK J v b hJ
  rw [norm_sub_sq_real]
  simp only [inner_smul_right, horth, mul_zero, sub_zero, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]

/-- The real growth parameter gives a lower bound on the residual norm. -/
theorem abs_parameter_mul_norm_le_residual (K : D →ₗ[ℝ] H)
    (hK : ∀ u v : D, inner ℝ (u : H) (K v) + inner ℝ (K u) (v : H) = 0)
    (J : H →ₗ[ℝ] H) (v : D) (a b : ℝ)
    (hJ : inner ℝ (v : H) (J (v : H)) = 0) :
    |a| * ‖(v : H)‖ ≤ ‖K v - b • J (v : H) - a • (v : H)‖ := by
  have hsquared : (|a| * ‖(v : H)‖) ^ 2 ≤
      ‖K v - b • J (v : H) - a • (v : H)‖ ^ 2 := by
    rw [mul_pow, sq_abs, residual_norm_sq K hK J v a b hJ]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hleft : 0 ≤ |a| * ‖(v : H)‖ := mul_nonneg (abs_nonneg a) (norm_nonneg _)
  have hright : 0 ≤ ‖K v - b • J (v : H) - a • (v : H)‖ := norm_nonneg _
  simpa only [abs_of_nonneg hleft, abs_of_nonneg hright] using (sq_le_sq.mp hsquared)

/-- For a normalized vector, the residual directly bounds the parameter. -/
theorem abs_parameter_le_residual_of_norm_eq_one (K : D →ₗ[ℝ] H)
    (hK : ∀ u v : D, inner ℝ (u : H) (K v) + inner ℝ (K u) (v : H) = 0)
    (J : H →ₗ[ℝ] H) (v : D) (a b : ℝ)
    (hJ : inner ℝ (v : H) (J (v : H)) = 0) (hv : ‖(v : H)‖ = 1) :
    |a| ≤ ‖K v - b • J (v : H) - a • (v : H)‖ := by
  simpa only [hv, mul_one] using abs_parameter_mul_norm_le_residual K hK J v a b hJ

/-- A nonzero exact mode has zero real growth parameter. -/
theorem parameter_eq_zero_of_exact_mode (K : D →ₗ[ℝ] H)
    (hK : ∀ u v : D, inner ℝ (u : H) (K v) + inner ℝ (K u) (v : H) = 0)
    (J : H →ₗ[ℝ] H) (v : D) (a b : ℝ)
    (hJ : inner ℝ (v : H) (J (v : H)) = 0) (hv : v ≠ 0)
    (hmode : K v = b • J (v : H) + a • (v : H)) : a = 0 := by
  have hbound := abs_parameter_mul_norm_le_residual K hK J v a b hJ
  have hzero : K v - b • J (v : H) - a • (v : H) = 0 := by
    rw [hmode, add_sub_cancel_left, sub_self]
  rw [hzero, norm_zero] at hbound
  have hproduct : |a| * ‖(v : H)‖ = 0 :=
    le_antisymm hbound (mul_nonneg (abs_nonneg a) (norm_nonneg _))
  have hvH : (v : H) ≠ 0 := by
    intro hz
    exact hv (Subtype.ext hz)
  exact abs_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right (norm_ne_zero_iff.mpr hvH))

end InfoGeometry.OperatorAlgebra.RealSkewDomainResidual
