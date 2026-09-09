import InfoGeometry.Canonical.HestenesCircularSheetCAR

/-!
# Hestenes phase, boost, and rotation rotor normal forms

This owner isolates the finite algebraic rotor certificates.  Analytic
`cosh/sinh` and `cos/sin` parameterizations can be added later as
specializations of the scalar constraints.
-/

noncomputable section
namespace HestenesPhaseBoostRotors

open TwoSheetThreeColorWeyl
open HestenesCircularSheetCAR

abbrev Sheet := M2C

def K : Sheet := sheetGamma
def IK : Sheet := Complex.I • K

def boostRotor (a b : ℂ) : Sheet := a • (1 : Sheet) + b • K
def boostReverse (a b : ℂ) : Sheet := a • (1 : Sheet) - b • K

def rotationRotor (a b : ℂ) : Sheet := a • (1 : Sheet) + b • IK
def rotationReverse (a b : ℂ) : Sheet := a • (1 : Sheet) - b • IK

@[simp] theorem K_sq : K * K = (1 : Sheet) := by
  exact sheet_parity.1

@[simp] theorem IK_sq : IK * IK = (-1 : ℂ) • (1 : Sheet) := by
  unfold IK
  simp [K_sq, smul_smul]

theorem boostRotor_mul_reverse (a b : ℂ) (h : a ^ 2 - b ^ 2 = 1) :
    boostRotor a b * boostReverse a b = (1 : Sheet) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [boostRotor, boostReverse, K, sheetGamma, sheetPlus,
      sheetMinus, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h

theorem rotationRotor_mul_reverse (a b : ℂ) (h : a ^ 2 + b ^ 2 = 1) :
    rotationRotor a b * rotationReverse a b = (1 : Sheet) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotationRotor, rotationReverse, IK, K, sheetGamma, sheetPlus,
      sheetMinus, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    rw [hI] <;>
    linear_combination h

end HestenesPhaseBoostRotors
end noncomputable section
