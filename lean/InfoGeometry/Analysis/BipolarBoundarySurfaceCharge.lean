import InfoGeometry.Analysis.BipolarBoundaryTrace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Analysis.BipolarBoundarySurfaceCharge

open MeasureTheory
open InfoGeometry.Analysis.BipolarBoundaryTrace

def boundaryKernel (y : ℝ) : ℝ := 1 / ((1 / 4 : ℝ) + y ^ 2)

theorem boundaryKernel_eq_deriv_phiXY_half (y : ℝ) :
    boundaryKernel y = deriv (fun x => phiXY x y) (1 / 2) :=
  (deriv_phiXY_half y).symm

theorem boundaryKernel_pos (y : ℝ) : 0 < boundaryKernel y := by
  unfold boundaryKernel
  positivity

theorem boundaryKernel_eq_four_mul_inv_one_add_sq (y : ℝ) :
    boundaryKernel y = 4 * (1 + ((2 : ℝ) * y) ^ 2)⁻¹ := by
  have h₀ : (1 / 4 : ℝ) + y ^ 2 ≠ 0 := by positivity
  have h₁ : (1 : ℝ) + ((2 : ℝ) * y) ^ 2 ≠ 0 := by positivity
  unfold boundaryKernel
  field_simp [h₀, h₁]
  ring

theorem integrable_boundaryKernel : Integrable boundaryKernel := by
  have hbase : Integrable (fun y : ℝ => (1 + ((2 : ℝ) * y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (by norm_num)
  have hscaled : Integrable (fun y : ℝ => 4 * (1 + ((2 : ℝ) * y) ^ 2)⁻¹) :=
    Integrable.const_mul hbase 4
  refine hscaled.congr ?_
  filter_upwards with y
  exact (boundaryKernel_eq_four_mul_inv_one_add_sq y).symm

theorem integral_boundaryKernel : (∫ y : ℝ, boundaryKernel y) = 2 * Real.pi := by
  simp_rw [boundaryKernel_eq_four_mul_inv_one_add_sq]
  rw [MeasureTheory.integral_const_mul]
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun x : ℝ => (1 + x ^ 2)⁻¹) (2 : ℝ)
  norm_num at h ⊢
  rw [h]
  ring

def scaledImagePotential (sourceStrength epsilon x y : ℝ) : ℝ :=
  -(sourceStrength / (2 * Real.pi * epsilon)) * phiXY x y

@[simp] theorem scaledImagePotential_half (sourceStrength epsilon y : ℝ) :
    scaledImagePotential sourceStrength epsilon (1 / 2) y = 0 := by
  rw [scaledImagePotential, phiXY_half]
  ring

theorem hasDerivAt_scaledImagePotential_half
    (sourceStrength epsilon y : ℝ) :
    HasDerivAt (fun x => scaledImagePotential sourceStrength epsilon x y)
      (-(sourceStrength / (2 * Real.pi * epsilon)) * boundaryKernel y) (1 / 2) := by
  simpa [scaledImagePotential, boundaryKernel] using
    (hasDerivAt_phiXY_half y).const_mul
      (-(sourceStrength / (2 * Real.pi * epsilon)))

theorem deriv_scaledImagePotential_half (sourceStrength epsilon y : ℝ) :
    deriv (fun x => scaledImagePotential sourceStrength epsilon x y) (1 / 2) =
      -(sourceStrength / (2 * Real.pi * epsilon)) * boundaryKernel y :=
  (hasDerivAt_scaledImagePotential_half sourceStrength epsilon y).deriv

def leftNormalDerivativeAtHalf (f : ℝ → ℝ) : ℝ := -deriv f (1 / 2)

def inducedSurfaceDensity (sourceStrength y : ℝ) : ℝ :=
  -(sourceStrength / (2 * Real.pi)) * boundaryKernel y

theorem inducedSurfaceDensity_eq_neg_epsilon_mul_leftNormalDerivative
    (sourceStrength epsilon y : ℝ) (hepsilon : epsilon ≠ 0) :
    inducedSurfaceDensity sourceStrength y =
      -epsilon * leftNormalDerivativeAtHalf
        (fun x => scaledImagePotential sourceStrength epsilon x y) := by
  rw [leftNormalDerivativeAtHalf, deriv_scaledImagePotential_half]
  unfold inducedSurfaceDensity
  field_simp [hepsilon, Real.pi_ne_zero]

theorem integrable_inducedSurfaceDensity (sourceStrength : ℝ) :
    Integrable (inducedSurfaceDensity sourceStrength) := by
  unfold inducedSurfaceDensity
  exact Integrable.const_mul integrable_boundaryKernel
    (-(sourceStrength / (2 * Real.pi)))

theorem integral_inducedSurfaceDensity (sourceStrength : ℝ) :
    (∫ y : ℝ, inducedSurfaceDensity sourceStrength y) = -sourceStrength := by
  unfold inducedSurfaceDensity
  rw [MeasureTheory.integral_const_mul, integral_boundaryKernel]
  field_simp [Real.pi_ne_zero]

theorem bipolar_boundary_surface_charge_packet
    (sourceStrength epsilon y : ℝ) (hepsilon : epsilon ≠ 0) :
    scaledImagePotential sourceStrength epsilon (1 / 2) y = 0 ∧
      deriv (fun x => scaledImagePotential sourceStrength epsilon x y) (1 / 2) =
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
