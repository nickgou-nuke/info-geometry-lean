import InfoGeometry.Analysis.BipolarBoundarySurfaceCharge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Finite-interval laws for the bipolar boundary kernel

`BipolarBoundarySurfaceCharge` already owns the boundary kernel, its
integrability, total mass `2π`, the normalized image density, and total balance
`-Q`. This file adds only the missing finite-interval readout.

The kernel has the exact arctangent primitive

`∫_a^b dy / (1/4+y²) = 2 (arctan(2b) - arctan(2a))`.

No second kernel definition or parallel physical normalization is introduced.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarBoundaryKernelIntegral

open scoped Interval

open InfoGeometry.Analysis.BipolarBoundarySurfaceCharge

/-- Native `c²+y²` normal form used by Mathlib's arctangent integral theorem. -/
theorem boundaryKernel_eq_half_sq (y : ℝ) :
    boundaryKernel y = (((1 / 2 : ℝ) ^ 2 + y ^ 2)⁻¹) := by
  norm_num [boundaryKernel, one_div]

/-- Exact finite-interval integral of the canonical boundary kernel. -/
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

/-- Symmetric truncation of the boundary-kernel mass. -/
def symmetricBoundaryMass (R : ℝ) : ℝ :=
  ∫ y in -R..R, boundaryKernel y

/-- Exact symmetric-truncation formula. -/
theorem symmetricBoundaryMass_eq (R : ℝ) :
    symmetricBoundaryMass R = 4 * Real.arctan (2 * R) := by
  rw [symmetricBoundaryMass, intervalIntegral_boundaryKernel]
  have harg : (2 : ℝ) * (-R) = -(2 * R) := by ring
  rw [harg, Real.arctan_neg]
  ring

/-- Finite-interval integral of the already-owned normalized image density. -/
theorem intervalIntegral_inducedSurfaceDensity
    (sourceStrength a b : ℝ) :
    (∫ y in a..b, inducedSurfaceDensity sourceStrength y) =
      -(sourceStrength / Real.pi) *
        (Real.arctan (2 * b) - Real.arctan (2 * a)) := by
  unfold inducedSurfaceDensity
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_boundaryKernel]
  field_simp [Real.pi_ne_zero]
  ring

/-- Compact finite/full boundary-mass packet. -/
theorem bipolar_boundary_kernel_interval_packet
    (sourceStrength a b : ℝ) :
    (∫ y in a..b, boundaryKernel y) =
        2 * (Real.arctan (2 * b) - Real.arctan (2 * a)) ∧
      (∫ y in a..b, inducedSurfaceDensity sourceStrength y) =
        -(sourceStrength / Real.pi) *
          (Real.arctan (2 * b) - Real.arctan (2 * a)) ∧
      (∫ y : ℝ, boundaryKernel y) = 2 * Real.pi ∧
      (∫ y : ℝ, inducedSurfaceDensity sourceStrength y) = -sourceStrength := by
  exact ⟨intervalIntegral_boundaryKernel a b,
    intervalIntegral_inducedSurfaceDensity sourceStrength a b,
    integral_boundaryKernel,
    integral_inducedSurfaceDensity sourceStrength⟩

end InfoGeometry.Analysis.BipolarBoundaryKernelIntegral
