import InfoGeometry.Analysis.BipolarBoundaryTrace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Normalized boundary density of the bipolar image potential

The intrinsic owner `BipolarBoundaryTrace` proves that the logarithmic bipolar
potential

`phiXY(x,y) = log |x+iy| - log |x-1+iy|`

vanishes on the vertical bisector `x=1/2` and has normal derivative

`1 / (1/4 + y^2)`.

This file adds a scalar image-charge normalization.  For source strength `Q`
and nonzero scale `epsilon`, define

`Phi = -Q / (2 pi epsilon) * phiXY`.

With the normal pointing from the bisector into the left half-plane, the
induced boundary density is

`sigma(y) = -Q / (2 pi) * 1 / (1/4 + y^2)`.

The Cauchy kernel is integrable with total mass `2 pi`, so the total induced
boundary strength is exactly `-Q`.

These are scalar analytic identities.  No Maxwell equation, material law,
perfect-conductor model, SI dimensional analysis, or superconducting
interpretation is built into the definitions.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarBoundarySurfaceCharge

open MeasureTheory
open InfoGeometry.Analysis.BipolarBoundaryTrace

/-- Positive Cauchy kernel occurring as the bisector normal derivative. -/
def boundaryKernel (y : ℝ) : ℝ :=
  1 / ((1 / 4 : ℝ) + y ^ 2)

/-- The boundary kernel is the genuine horizontal derivative of the intrinsic
logarithmic potential on `x=1/2`. -/
theorem boundaryKernel_eq_deriv_phiXY_half (y : ℝ) :
    boundaryKernel y = deriv (fun x => phiXY x y) (1 / 2) := by
  exact (deriv_phiXY_half y).symm

/-- The boundary kernel is strictly positive. -/
theorem boundaryKernel_pos (y : ℝ) :
    0 < boundaryKernel y := by
  unfold boundaryKernel
  positivity

/-- Rescaling to the standard Cauchy kernel. -/
theorem boundaryKernel_eq_four_mul_inv_one_add_sq (y : ℝ) :
    boundaryKernel y =
      4 * (1 + ((2 : ℝ) * y) ^ 2)⁻¹ := by
  have h₀ : (1 / 4 : ℝ) + y ^ 2 ≠ 0 := by positivity
  have h₁ : (1 : ℝ) + ((2 : ℝ) * y) ^ 2 ≠ 0 := by positivity
  unfold boundaryKernel
  field_simp [h₀, h₁]
  ring

/-- The boundary kernel is integrable on the full real bisector. -/
theorem integrable_boundaryKernel :
    Integrable boundaryKernel := by
  have hbase :
      Integrable (fun y : ℝ =>
        (1 + ((2 : ℝ) * y) ^ 2)⁻¹) :=
    integrable_inv_one_add_mul_sq (by norm_num)
  have hscaled :
      Integrable (fun y : ℝ =>
        4 * (1 + ((2 : ℝ) * y) ^ 2)⁻¹) :=
    Integrable.const_mul hbase 4
  simpa only [boundaryKernel_eq_four_mul_inv_one_add_sq] using hscaled

/-- Exact total mass of the bisector Cauchy kernel. -/
theorem integral_boundaryKernel :
    (∫ y : ℝ, boundaryKernel y) = 2 * Real.pi := by
  simp_rw [boundaryKernel_eq_four_mul_inv_one_add_sq]
  rw [MeasureTheory.integral_const_mul,
    integral_univ_inv_one_add_mul_sq (2 : ℝ)]
  norm_num
  ring

/-- Image-normalized scalar potential.  The parameter `epsilon` is kept
explicit; a physical permittivity interpretation is additional data. -/
def scaledImagePotential
    (sourceStrength epsilon x y : ℝ) : ℝ :=
  -(sourceStrength / (2 * Real.pi * epsilon)) * phiXY x y

/-- The normalized potential still vanishes on the bisector. -/
@[simp] theorem scaledImagePotential_half
    (sourceStrength epsilon y : ℝ) :
    scaledImagePotential sourceStrength epsilon (1 / 2) y = 0 := by
  simp [scaledImagePotential]

/-- Genuine horizontal derivative of the normalized potential on the
bisector. -/
theorem hasDerivAt_scaledImagePotential_half
    (sourceStrength epsilon y : ℝ) :
    HasDerivAt
      (fun x => scaledImagePotential sourceStrength epsilon x y)
      (-(sourceStrength / (2 * Real.pi * epsilon)) * boundaryKernel y)
      (1 / 2) := by
  simpa [scaledImagePotential, boundaryKernel] using
    (hasDerivAt_phiXY_half y).const_mul
      (-(sourceStrength / (2 * Real.pi * epsilon)))

/-- Ordinary derivative readout of the normalized potential. -/
theorem deriv_scaledImagePotential_half
    (sourceStrength epsilon y : ℝ) :
    deriv (fun x => scaledImagePotential sourceStrength epsilon x y)
      (1 / 2) =
        -(sourceStrength / (2 * Real.pi * epsilon)) * boundaryKernel y := by
  exact (hasDerivAt_scaledImagePotential_half
    sourceStrength epsilon y).deriv

/-- Normal derivative for the unit normal pointing into the left half-plane. -/
def leftNormalDerivativeAtHalf (f : ℝ → ℝ) : ℝ :=
  -deriv f (1 / 2)

/-- Induced scalar boundary density in the image normalization. -/
def inducedSurfaceDensity (sourceStrength y : ℝ) : ℝ :=
  -(sourceStrength / (2 * Real.pi)) * boundaryKernel y

/-- The density is obtained from the normalized potential by the standard
oriented boundary expression `-epsilon * partial_n Phi`, provided the scale is
nonzero. -/
theorem inducedSurfaceDensity_eq_neg_epsilon_mul_leftNormalDerivative
    (sourceStrength epsilon y : ℝ) (hepsilon : epsilon ≠ 0) :
    inducedSurfaceDensity sourceStrength y =
      -epsilon * leftNormalDerivativeAtHalf
        (fun x => scaledImagePotential sourceStrength epsilon x y) := by
  rw [leftNormalDerivativeAtHalf,
    deriv_scaledImagePotential_half]
  unfold inducedSurfaceDensity
  field_simp [hepsilon, Real.pi_ne_zero]
  ring

/-- The induced density is integrable for every source strength. -/
theorem integrable_inducedSurfaceDensity (sourceStrength : ℝ) :
    Integrable (inducedSurfaceDensity sourceStrength) := by
  unfold inducedSurfaceDensity
  exact Integrable.const_mul integrable_boundaryKernel
    (-(sourceStrength / (2 * Real.pi)))

/-- Exact image-charge balance: the full induced boundary strength is the
negative of the source strength. -/
theorem integral_inducedSurfaceDensity (sourceStrength : ℝ) :
    (∫ y : ℝ, inducedSurfaceDensity sourceStrength y) = -sourceStrength := by
  unfold inducedSurfaceDensity
  rw [MeasureTheory.integral_const_mul, integral_boundaryKernel]
  field_simp [Real.pi_ne_zero]
  ring

/-- Compact normalized-boundary packet. -/
theorem bipolar_boundary_surface_charge_packet
    (sourceStrength epsilon y : ℝ) (hepsilon : epsilon ≠ 0) :
    scaledImagePotential sourceStrength epsilon (1 / 2) y = 0 ∧
      deriv (fun x => scaledImagePotential sourceStrength epsilon x y)
          (1 / 2) =
        -(sourceStrength / (2 * Real.pi * epsilon)) * boundaryKernel y ∧
      inducedSurfaceDensity sourceStrength y =
        -epsilon * leftNormalDerivativeAtHalf
          (fun x => scaledImagePotential sourceStrength epsilon x y) ∧
      Integrable (inducedSurfaceDensity sourceStrength) ∧
      (∫ t : ℝ, inducedSurfaceDensity sourceStrength t) = -sourceStrength := by
  exact ⟨scaledImagePotential_half sourceStrength epsilon y,
    deriv_scaledImagePotential_half sourceStrength epsilon y,
    inducedSurfaceDensity_eq_neg_epsilon_mul_leftNormalDerivative
      sourceStrength epsilon y hepsilon,
    integrable_inducedSurfaceDensity sourceStrength,
    integral_inducedSurfaceDensity sourceStrength⟩

end InfoGeometry.Analysis.BipolarBoundarySurfaceCharge
