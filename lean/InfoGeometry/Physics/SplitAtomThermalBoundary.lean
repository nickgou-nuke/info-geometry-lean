import InfoGeometry.Canonical.KMSSubstateKMSCondition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# A positive two-level density and its finite KMS boundary

The positive density uses a real parameter.  It is not exp((eta+i theta)J).
The existing owner uses physical evolution rho^(-it) A rho^(it), whose
upper imaginary boundary is rho A rho^(-1).  For the opposite modular
convention rho^(it) A rho^(-it), the upper boundary has the inverse order.
Only the finite algebraic boundary identities are asserted here; holomorphic
strip control and Tomita--Takesaki modular operators are separate objects.
-/

noncomputable section

namespace InfoGeometry.Physics.SplitAtomThermalBoundary

open InfoGeometry.Canonical

abbrev CMat2 := InfoGeometry.Algebra.FiniteSpin.Mat2C

def partition (eta : ℝ) : ℝ := Real.exp eta + Real.exp (-eta)

theorem partition_pos (eta : ℝ) : 0 < partition eta :=
  add_pos (Real.exp_pos _) (Real.exp_pos _)

def p (eta : ℝ) : ℝ := Real.exp eta / partition eta

def q (eta : ℝ) : ℝ := Real.exp (-eta) / partition eta

theorem p_pos (eta : ℝ) : 0 < p eta := div_pos (Real.exp_pos _) (partition_pos _)

theorem q_pos (eta : ℝ) : 0 < q eta := div_pos (Real.exp_pos _) (partition_pos _)

theorem p_add_q (eta : ℝ) : p eta + q eta = 1 := by
  dsimp [p, q]
  rw [← add_div]
  change partition eta / partition eta = 1
  exact div_self (ne_of_gt (partition_pos eta))

def density (eta : ℝ) : CMat2 := !![(p eta : ℂ), 0; 0, (q eta : ℂ)]

def inverseDensity (eta : ℝ) : CMat2 :=
  !![(p eta : ℂ)⁻¹, 0; 0, (q eta : ℂ)⁻¹]

theorem density_mul_inverse (eta : ℝ) : density eta * inverseDensity eta = 1 := by
  have hp : (p eta : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (p_pos eta))
  have hq : (q eta : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (q_pos eta))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [density, inverseDensity, Matrix.mul_apply, Fin.sum_univ_two, hp, hq]

theorem inverse_mul_density (eta : ℝ) : inverseDensity eta * density eta = 1 := by
  have hp : (p eta : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (p_pos eta))
  have hq : (q eta : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (q_pos eta))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [density, inverseDensity, Matrix.mul_apply, Fin.sum_univ_two, hp, hq]

def densityUnit (eta : ℝ) : CMat2ˣ where
  val := density eta
  inv := inverseDensity eta
  val_inv := density_mul_inverse eta
  inv_val := inverse_mul_density eta

theorem state_readout (eta : ℝ) (A : CMat2) :
    thermalState (density eta) A = (p eta : ℂ) * A 0 0 + (q eta : ℂ) * A 1 1 := by
  simp [thermalState, density, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]

theorem state_normalized (eta : ℝ) : thermalState (density eta) (1 : CMat2) = 1 := by
  rw [state_readout]
  simpa only [Matrix.one_apply_eq, mul_one, ← Complex.ofReal_add,
    Complex.ofReal_one] using congrArg (fun r : ℝ => (r : ℂ)) (p_add_q eta)

/-- Positivity of the existing functional is obtained from explicit squares. -/
theorem state_square_readout (eta : ℝ) (A : CMat2) :
    (thermalState (density eta) (A.conjTranspose * A)).re =
      p eta * ((A 0 0).re ^ 2 + (A 0 0).im ^ 2 +
        (A 1 0).re ^ 2 + (A 1 0).im ^ 2) +
      q eta * ((A 0 1).re ^ 2 + (A 0 1).im ^ 2 +
        (A 1 1).re ^ 2 + (A 1 1).im ^ 2) := by
  rw [state_readout]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.star_def]
  ring

theorem state_positive (eta : ℝ) (A : CMat2) :
    0 ≤ (thermalState (density eta) (A.conjTranspose * A)).re := by
  rw [state_square_readout]
  have hp := p_pos eta
  have hq := q_pos eta
  positivity

theorem state_square_im_zero (eta : ℝ) (A : CMat2) :
    (thermalState (density eta) (A.conjTranspose * A)).im = 0 := by
  rw [state_readout]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Complex.mul_im, Complex.star_def] <;> ring

/-- The inverse hypotheses of the existing KMS owner are now discharged. -/
theorem physical_upper_boundary (eta : ℝ) (A B : CMat2) :
    thermalState (density eta)
      (A * modularAutomorphism_i (density eta) (inverseDensity eta) B) =
        thermalState (density eta) (B * A) :=
  kms_condition_beta_one _ _ _ _ (inverse_mul_density eta) (density_mul_inverse eta)

/-- Opposite time convention: upper boundary applied to the first factor. -/
theorem modular_upper_boundary (eta : ℝ) (A B : CMat2) :
    thermalState (density eta) ((inverseDensity eta * A * density eta) * B) =
      thermalState (density eta) (B * A) := by
  dsimp [thermalState]
  have hprod : density eta * ((inverseDensity eta * A * density eta) * B) =
      A * (density eta * B) := by
    calc
      _ = (density eta * inverseDensity eta) * (A * (density eta * B)) := by
        noncomm_ring
      _ = _ := by rw [density_mul_inverse, one_mul]
  rw [hprod, Matrix.trace_mul_comm A (density eta * B), Matrix.mul_assoc]

end InfoGeometry.Physics.SplitAtomThermalBoundary
