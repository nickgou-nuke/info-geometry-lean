import InfoGeometry.Dynamics.ParaKahlerJKORicciFlowBridge
import InfoGeometry.Dynamics.WassersteinProximalBridge

noncomputable section

namespace InfoGeometry.Dynamics.ParaKahlerJKOCompositionBridge

open Matrix
open InfoGeometry.Dynamics.ParaKahlerJKORicciFlow
open InfoGeometry.Dynamics.WassersteinProximalBridge

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! A coefficientwise lift from the real finite shear carrier to the complex one. -/
def complexify (A : M2R) : M2C := fun i j => (A i j : ℂ)

/-- The real Para-Kähler shear and the existing complex proximal step have the
same explicit matrix after coefficientwise complexification. -/
theorem complexify_jkoStep_eq_realStepAsComplex (t : ℝ) :
    complexify (jkoStep t) = realStepAsComplex t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexify, jkoStep_matrix, realStepAsComplex,
      InfoGeometry.Canonical.RealParabolicProximal.step]

/-- The finite real shear therefore inherits the additive composition law of
the complex proximal carrier after complexification. -/
theorem complexify_jkoStep_composition (s t : ℝ) :
    complexify (jkoStep s) * complexify (jkoStep t) =
      complexify (jkoStep (s + t)) := by
  rw [complexify_jkoStep_eq_realStepAsComplex,
    complexify_jkoStep_eq_realStepAsComplex,
    complexify_jkoStep_eq_realStepAsComplex]
  exact realStepAsComplex_composition s t

/-- Complexification preserves the explicit inverse of the finite shear. -/
theorem complexify_jkoStep_mul_neg (t : ℝ) :
    complexify (jkoStep t) * complexify (jkoStep (-t)) = 1 := by
  rw [complexify_jkoStep_eq_realStepAsComplex,
    complexify_jkoStep_eq_realStepAsComplex]
  exact realStepAsComplex_mul_neg t

/-- The inverse law also holds in the opposite multiplication order. -/
theorem complexify_jkoStep_neg_mul (t : ℝ) :
    complexify (jkoStep (-t)) * complexify (jkoStep t) = 1 := by
  rw [complexify_jkoStep_eq_realStepAsComplex,
    complexify_jkoStep_eq_realStepAsComplex]
  exact realStepAsComplex_neg_mul t

/-- Iterating the real shear and then complexifying agrees with the accumulated
complex proximal step. -/
theorem complexify_jkoStep_pow (t : ℝ) (n : ℕ) :
    complexify (jkoStep t) ^ n = complexify (jkoStep ((n : ℝ) * t)) := by
  rw [complexify_jkoStep_eq_realStepAsComplex,
    complexify_jkoStep_eq_realStepAsComplex]
  exact realStepAsComplex_pow t n

end InfoGeometry.Dynamics.ParaKahlerJKOCompositionBridge
