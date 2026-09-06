import proofs.TwelveFoldSheetColorOmega
import proofs.HestenesCircularSheetCAR

/-!
# Quartic phase action on the circular CAR basis

The sheet phase is an associative matrix-layer operator.  This owner records
its action on the circular nilpotents without identifying the matrix algebra
with a split-octonion product.
-/

noncomputable section
namespace CircularCARQuarticCapstone

open TwoSheetThreeColorWeyl
open HestenesCircularSheetCAR
open TwelveFoldSheetColorOmega

abbrev Sheet := M2C

def omegaChiInv : Sheet := sheetPlus - Complex.I • sheetMinus

@[simp] theorem omegaChi_mul_inv :
    omegaSheet * omegaChiInv = (1 : Sheet) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaSheet, omegaChiInv, sheetPlus, sheetMinus,
      sheetGamma, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem inv_mul_omegaChi :
    omegaChiInv * omegaSheet = (1 : Sheet) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaSheet, omegaChiInv, sheetPlus, sheetMinus,
      sheetGamma, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem omegaChi_cPlus_phase :
    omegaSheet * cPlus * omegaChiInv = (-Complex.I) • cPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaSheet, omegaChiInv, cPlus, sheetGamma, sheetPlus,
      sheetMinus, sheetFlip, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem omegaChi_cMinus_phase :
    omegaSheet * cMinus * omegaChiInv = Complex.I • cMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaSheet, omegaChiInv, cMinus, sheetGamma, sheetPlus,
      sheetMinus, sheetFlip, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem circular_car_quartic_packet :
    cPlus * cPlus = 0 ∧
      cMinus * cMinus = 0 ∧
      cPlus * cMinus = uPlus ∧
      cMinus * cPlus = uMinus ∧
      omegaSheet * cPlus * omegaChiInv = (-Complex.I) • cPlus ∧
      omegaSheet * cMinus * omegaChiInv = Complex.I • cMinus := by
  exact ⟨cPlus_sq, cMinus_sq, cPlus_cMinus, cMinus_cPlus,
    omegaChi_cPlus_phase, omegaChi_cMinus_phase⟩

end CircularCARQuarticCapstone
end noncomputable section
