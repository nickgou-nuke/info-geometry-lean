import InfoGeometry.Analysis.BipolarBoundaryTrace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Integral of the bipolar boundary kernel

The normal derivative of the real bipolar potential on the vertical bisector is

`1 / (1/4 + y^2)`.

This file treats that function first as a purely mathematical Cauchy kernel. It
proves its finite-interval antiderivative, integrability on the real line, and
exact total mass `2π`. A separately named normalization with total mass `-Q`
records the algebra that a downstream boundary-source model may reuse.

No permittivity, electric charge unit, conductor, or boundary-value uniqueness
theorem is built into the intrinsic kernel.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarBoundaryKernelIntegral

open MeasureTheory
open scoped Interval

open InfoGeometry.Analysis.BipolarBoundaryTrace

/-- Cauchy kernel appearing as the normal derivative on the critical
bisector. -/
def boundaryKernel (y : ℝ) : ℝ :=
  1 / ((1 / 4 : ℝ) + y ^ 2)

/-- The boundary kernel is the exact normal derivative already proved for the
bipolar potential. -/
theorem boundaryKernel_eq_normalDerivative (y : ℝ) :
    boundaryKernel y = deriv (fun x => phiXY x y) (1 / 2) := by
  simpa [boundaryKernel] using (deriv_phiXY_half y).symm

/-- Standard scaled-Cauchy normal form. -/
theorem boundaryKernel_eq_scaledCauchy (y : ℝ) :
    boundaryKernel y = 4 * (1 + (2 * y) ^ 2)⁻¹ := by
  have hleft : (1 / 4 : ℝ) + y ^ 2 ≠ 0 := by positivity
  have hright : (1 : ℝ) + (2 * y) ^ 2 ≠ 0 := by positivity
  unfold boundaryKernel
  field_simp [hleft, hright]
  ring

/-- The same kernel in the native `c^2+x^2` form used by Mathlib's arctangent
integral theorem. -/
theorem boundaryKernel_eq_half_sq (y : ℝ) :
    boundaryKernel y = (((1 / 2 : ℝ) ^ 2 + y ^ 2)⁻¹) := by
  norm_num [boundaryKernel, one_div]

/-- Exact finite-interval integral of the boundary kernel. -/
theorem intervalIntegral_boundaryKernel (a b : ℝ) :
    (∫ y in a..b, boundaryKernel y) =
      2 * (Real.arctan (2 * b) - Real.arctan (2 * a)) := by
  have hfun :
      boundaryKernel = fun y : ℝ => ((1 / 2 : ℝ) ^ 2 + y ^ 2)⁻¹ := by
    funext y
    exact boundaryKernel_eq_half_sq y
  rw [hfun]
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.integral_inv_sq_add_sq
      (a := a) (b := b) (c := (1 / 2 : ℝ)) (by norm_num))

/-- The boundary kernel is integrable on the complete real line. -/
theorem integrable_boundaryKernel : Integrable boundaryKernel := by
  have hfun :
      boundaryKernel = fun y : ℝ => 4 * (1 + (2 * y) ^ 2)⁻¹ := by
    funext y
    exact boundaryKernel_eq_scaledCauchy y
  rw [hfun]
  exact
    (Real.integrable_inv_one_add_mul_sq
      (b := (2 : ℝ)) (by norm_num)).const_mul 4

/-- Exact total mass of the Cauchy kernel. -/
theorem integral_boundaryKernel :
    (∫ y : ℝ, boundaryKernel y) = 2 * Real.pi := by
  have hfun :
      boundaryKernel = fun y : ℝ => 4 * (1 + (2 * y) ^ 2)⁻¹ := by
    funext y
    exact boundaryKernel_eq_scaledCauchy y
  rw [hfun, integral_const_mul,
    Real.integral_univ_inv_one_add_mul_sq]
  norm_num [abs_of_nonneg]
  ring

/-- Boundary density normalized to have total mass `-Q`. -/
def normalizedBoundaryDensity (Q y : ℝ) : ℝ :=
  -(Q / (2 * Real.pi)) * boundaryKernel y

/-- The normalized density remains integrable. -/
theorem integrable_normalizedBoundaryDensity (Q : ℝ) :
    Integrable (normalizedBoundaryDensity Q) := by
  unfold normalizedBoundaryDensity
  exact integrable_boundaryKernel.const_mul _

/-- The normalization is exact: its real-line integral is `-Q`. -/
theorem integral_normalizedBoundaryDensity (Q : ℝ) :
    (∫ y : ℝ, normalizedBoundaryDensity Q y) = -Q := by
  unfold normalizedBoundaryDensity
  rw [integral_const_mul, integral_boundaryKernel]
  field_simp [Real.pi_ne_zero]
  ring

/-- Compact intrinsic/normalized boundary-kernel packet. -/
theorem bipolar_boundary_kernel_packet (Q : ℝ) :
    (∀ y, boundaryKernel y = deriv (fun x => phiXY x y) (1 / 2)) ∧
      Integrable boundaryKernel ∧
      (∫ y : ℝ, boundaryKernel y) = 2 * Real.pi ∧
      Integrable (normalizedBoundaryDensity Q) ∧
      (∫ y : ℝ, normalizedBoundaryDensity Q y) = -Q := by
  exact ⟨boundaryKernel_eq_normalDerivative,
    integrable_boundaryKernel,
    integral_boundaryKernel,
    integrable_normalizedBoundaryDensity Q,
    integral_normalizedBoundaryDensity Q⟩

end InfoGeometry.Analysis.BipolarBoundaryKernelIntegral
