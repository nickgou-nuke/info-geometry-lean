import InfoGeometry.Canonical.TwoSheetThreeColorWeylFinite
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hestenes circular sheet/CAR basis

This owner proves the split-idempotent and circular nilpotent identities in the
already validated Pauli sheet algebra.  It is the concrete matrix-side seed
for a later real `Cl⁺(1,3)` bridge; it does not claim that bridge by notation.
-/

noncomputable section
namespace HestenesCircularSheetCAR

open TwoSheetThreeColorWeyl

abbrev Sheet := M2C

def uPlus : Sheet := (1 / 2 : ℂ) • ((1 : Sheet) + sheetGamma)
def uMinus : Sheet := (1 / 2 : ℂ) • ((1 : Sheet) - sheetGamma)

def cPlus : Sheet := (1 / 2 : ℂ) • (sheetFlip + sheetGamma * sheetFlip)
def cMinus : Sheet := (1 / 2 : ℂ) • (sheetFlip - sheetGamma * sheetFlip)

@[simp] theorem uPlus_sq : uPlus * uPlus = uPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uPlus, sheetGamma, sheetPlus, sheetMinus,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem uMinus_sq : uMinus * uMinus = uMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uMinus, sheetGamma, sheetPlus, sheetMinus,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem uPlus_uMinus : uPlus * uMinus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, sheetGamma, sheetPlus, sheetMinus,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem uMinus_uPlus : uMinus * uPlus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, sheetGamma, sheetPlus, sheetMinus,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem uPlus_add_uMinus : uPlus + uMinus = (1 : Sheet) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, sheetGamma, sheetPlus, sheetMinus] <;> norm_num

@[simp] theorem cPlus_sq : cPlus * cPlus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cPlus, sheetGamma, sheetPlus, sheetMinus, sheetFlip,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem cMinus_sq : cMinus * cMinus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cMinus, sheetGamma, sheetPlus, sheetMinus, sheetFlip,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem cPlus_cMinus : cPlus * cMinus = uPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cPlus, cMinus, uPlus, sheetGamma, sheetPlus, sheetMinus,
      sheetFlip, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem cMinus_cPlus : cMinus * cPlus = uMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cPlus, cMinus, uMinus, sheetGamma, sheetPlus, sheetMinus,
      sheetFlip, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

end HestenesCircularSheetCAR
end noncomputable section
