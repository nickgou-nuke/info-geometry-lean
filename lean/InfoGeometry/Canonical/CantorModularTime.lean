import Mathlib.Tactic
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFColimitRepresentationBridge
import InfoGeometry.Canonical.OmegaBoundaryRepresentation
import InfoGeometry.Canonical.CantorDiracPropagation

/-!
# Emergent Time and Tomita-Takesaki Modular Dynamics

This module formalizes the emergence of time evolution from the thermodynamic KMS state.
We define the 1-parameter automorphism time scale factor `timeScale t` (representing $2^{-it}$),
define the modular time evolution action on the boundary Cuntz isometries, and prove that
it preserves all Cuntz algebra relations at all times `t`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorModularTime

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.OmegaBoundaryRepresentation
open InfoGeometry.Canonical.CantorDiracPropagation

/-- The modular time-scale factor $2^{-it}$ represented as a complex number. -/
def timeScale (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t * Real.log 2))

theorem timeScale_zero : timeScale 0 = 1 := by
  dsimp [timeScale]
  simp

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

/-- The modular time evolution of the left Cuntz isometry. -/
def sigma_L (t : ℝ) : CantorOp :=
  timeScale t • S_L_linear

/-- The modular time evolution of the left Cuntz adjoint. -/
def star_sigma_L (t : ℝ) : CantorOp :=
  (timeScale t)⁻¹ • star_S_L_linear

/-- The modular time evolution of the right Cuntz isometry. -/
def sigma_R (t : ℝ) : CantorOp :=
  timeScale t • S_R_linear

/-- The modular time evolution of the right Cuntz adjoint. -/
def star_sigma_R (t : ℝ) : CantorOp :=
  (timeScale t)⁻¹ • star_S_R_linear

theorem sigma_L_add (s t : ℝ) :
    sigma_L (s + t) = timeScale s • sigma_L t := by
  simp [sigma_L, timeScale_mul, smul_smul, mul_comm]

theorem sigma_R_add (s t : ℝ) :
    sigma_R (s + t) = timeScale s • sigma_R t := by
  simp [sigma_R, timeScale_mul, smul_smul, mul_comm]

/-- The modular time evolution preserves the left isometry relation `s* s = 1`. -/
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

/-- The modular time evolution preserves the right isometry relation `s* s = 1`. -/
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

/-- The modular time evolution preserves the orthogonal branch relation `sL* sR = 0`. -/
theorem sigma_L_star_sigma_R (t : ℝ) :
    star_sigma_L t * sigma_R t = 0 := by
  ext f x
  dsimp [star_sigma_L, sigma_R]
  rw [LinearMap.map_smul]
  dsimp [star_S_L_linear, S_R_linear]
  rw [star_S_L_op_S_R_op]
  simp

/-- The modular time evolution preserves the Cuntz partition of unity `sL sL* + sR sR* = 1`. -/
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

/-- The modular time evolved boundary Dirac operator. -/
def sigma_Dirac (t : ℝ) : CantorOp :=
  sigma_L t * star_sigma_R t + sigma_R t * star_sigma_L t

/-- Time-invariance of the boundary Dirac operator (Conservation of Energy). -/
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
