import Mathlib.Tactic
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFColimitRepresentationBridge
import InfoGeometry.Canonical.OmegaBoundaryRepresentation
import InfoGeometry.Canonical.CantorDiracPropagation

/-!
# Phase-Scaled Cantor Branch Generators

This module defines a multiplicative complex phase and scales the explicit
binary branch generators by that phase. It proves the resulting algebraic
relations. It does not construct a KMS state, a strongly continuous
automorphism group, or a Tomita--Takesaki modular flow.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorModularTime

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.OmegaBoundaryRepresentation
open InfoGeometry.Canonical.CantorDiracPropagation

/-- The phase factor `exp (-I * t * log 2)` used by the finite readout. -/
def timeScale (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t * Real.log 2))

theorem timeScale_zero : timeScale 0 = 1 := by
  dsimp [timeScale]
  simp

theorem norm_timeScale (t : ℝ) : ‖timeScale t‖ = 1 := by
  rw [timeScale]
  convert Complex.norm_exp_ofReal_mul_I (-(t * Real.log 2)) using 1 <;>
    push_cast <;> ring

theorem timeScale_mul (t1 t2 : ℝ) : timeScale (t1 + t2) = timeScale t1 * timeScale t2 := by
  dsimp [timeScale]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem timeScale_inv (t : ℝ) : timeScale (-t) = (timeScale t)⁻¹ := by
  dsimp [timeScale]
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- The phase-scaled left branch generator. -/
def sigma_L (t : ℝ) : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  timeScale t • S_L_linear

/-- The inverse-phase-scaled left adjoint generator. -/
def star_sigma_L (t : ℝ) : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  (timeScale t)⁻¹ • star_S_L_linear

/-- The phase-scaled right branch generator. -/
def sigma_R (t : ℝ) : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  timeScale t • S_R_linear

/-- The inverse-phase-scaled right adjoint generator. -/
def star_sigma_R (t : ℝ) : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  (timeScale t)⁻¹ • star_S_R_linear

theorem sigma_L_add (s t : ℝ) :
    sigma_L (s + t) = timeScale s • sigma_L t := by
  simp [sigma_L, timeScale_mul, smul_smul, mul_comm]

theorem sigma_R_add (s t : ℝ) :
    sigma_R (s + t) = timeScale s • sigma_R t := by
  simp [sigma_R, timeScale_mul, smul_smul, mul_comm]

theorem star_sigma_L_add (s t : ℝ) :
    star_sigma_L (s + t) = (timeScale s)⁻¹ • star_sigma_L t := by
  simp [star_sigma_L, timeScale_mul, smul_smul, mul_comm]

theorem star_sigma_R_add (s t : ℝ) :
    star_sigma_R (s + t) = (timeScale s)⁻¹ • star_sigma_R t := by
  simp [star_sigma_R, timeScale_mul, smul_smul, mul_comm]

/-- The phase-scaled left pair preserves `s* s = 1`. -/
theorem sigma_L_star_sigma_L (t : ℝ) :
    star_sigma_L t * sigma_L t = 1 := by
  ext f x
  dsimp [star_sigma_L, sigma_L]
  rw [LinearMap.map_smul]
  dsimp [star_S_L_linear, S_L_linear]
  rw [star_S_L_op_S_L_op]
  have h_nonzero : timeScale t ≠ 0 := by
    exact Complex.exp_ne_zero _
  rw [← mul_assoc, inv_mul_cancel₀ h_nonzero, one_mul]

/-- The phase-scaled right pair preserves `s* s = 1`. -/
theorem sigma_R_star_sigma_R (t : ℝ) :
    star_sigma_R t * sigma_R t = 1 := by
  ext f x
  dsimp [star_sigma_R, sigma_R]
  rw [LinearMap.map_smul]
  dsimp [star_S_R_linear, S_R_linear]
  rw [star_S_R_op_S_R_op]
  have h_nonzero : timeScale t ≠ 0 := by
    exact Complex.exp_ne_zero _
  rw [← mul_assoc, inv_mul_cancel₀ h_nonzero, one_mul]

/-- The phase-scaled branches remain orthogonal. -/
theorem sigma_L_star_sigma_R (t : ℝ) :
    star_sigma_L t * sigma_R t = 0 := by
  ext f x
  dsimp [star_sigma_L, sigma_R]
  rw [LinearMap.map_smul]
  dsimp [star_S_L_linear, S_R_linear]
  rw [star_S_L_op_S_R_op]
  simp

theorem sigma_R_star_sigma_L (t : ℝ) :
    star_sigma_R t * sigma_L t = 0 := by
  ext f x
  dsimp [star_sigma_R, sigma_L]
  rw [LinearMap.map_smul]
  dsimp [star_S_R_linear, S_L_linear]
  rw [star_S_R_op_S_L_op]
  simp

/-- The phase-scaled branches preserve the partition relation. -/
theorem sigma_Cuntz_partition (t : ℝ) :
    sigma_L t * star_sigma_L t + sigma_R t * star_sigma_R t = 1 := by
  ext f x
  dsimp [sigma_L, star_sigma_L, sigma_R, star_sigma_R]
  rw [LinearMap.map_smul, LinearMap.map_smul]
  dsimp [star_S_L_linear, S_L_linear, star_S_R_linear, S_R_linear]
  have h_nonzero : timeScale t ≠ 0 := by
    exact Complex.exp_ne_zero _
  rw [← mul_assoc, mul_inv_cancel₀ h_nonzero, one_mul]
  rw [← mul_assoc, mul_inv_cancel₀ h_nonzero, one_mul]
  exact congrFun (cuntz_partition_op f) x

/-- The cross-branch operator formed from the phase-scaled generators. -/
def sigma_Dirac (t : ℝ) : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  sigma_L t * star_sigma_R t + sigma_R t * star_sigma_L t

/-- The inverse phase cancels in the cross-branch operator. -/
theorem sigma_Dirac_eq_DiracOp (t : ℝ) :
    sigma_Dirac t = DiracOp := by
  ext f x
  dsimp [sigma_Dirac, DiracOp, sigma_L, star_sigma_R, sigma_R, star_sigma_L]
  rw [LinearMap.map_smul, LinearMap.map_smul]
  dsimp [star_S_L_linear, S_L_linear, star_S_R_linear, S_R_linear]
  have h_nonzero : timeScale t ≠ 0 := by
    exact Complex.exp_ne_zero _
  rw [← mul_assoc, mul_inv_cancel₀ h_nonzero, one_mul]
  rw [← mul_assoc, mul_inv_cancel₀ h_nonzero, one_mul]

end InfoGeometry.Canonical.CantorModularTime

end noncomputable section
