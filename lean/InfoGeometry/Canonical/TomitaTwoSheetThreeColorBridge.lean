import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped Matrix

namespace InfoGeometry.Canonical.TomitaTwoSheetThreeColorBridge

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

abbrev Mat23C := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

def sixthRootLift : Mat23C :=
  Matrix.kronecker sheetParity colorShift

def liftedParity : Mat23C :=
  Matrix.kronecker sheetParity (1 : Mat3C)

def positiveSheet : Mat23C :=
  Matrix.kronecker uPlus (1 : Mat3C)

def negativeSheet : Mat23C :=
  Matrix.kronecker uMinus (1 : Mat3C)

@[simp] theorem sheetParity_cube : sheetParity ^ 3 = sheetParity := by
  calc
    sheetParity ^ 3 = (sheetParity * sheetParity) * sheetParity := by
      simp [pow_two, pow_succ, mul_assoc]
    _ = sheetParity := by rw [sheetParity_sq]; simp

theorem sixthRootLift_cube : sixthRootLift ^ 3 = liftedParity := by
  rw [sixthRootLift, kronecker_pow_three, sheetParity_cube,
    colorShift_cubed]
  rfl

theorem sixthRootLift_sixth : sixthRootLift ^ 6 = 1 := by
  calc
    sixthRootLift ^ 6 = (sixthRootLift ^ 3) ^ 2 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
    _ = liftedParity ^ 2 := by rw [sixthRootLift_cube]
    _ = 1 := by
      rw [liftedParity, kronecker_pow_two,
        show sheetParity ^ 2 = 1 by simpa [pow_two] using sheetParity_sq]
      simp

theorem uPlus_mul_sheetParity : uPlus * sheetParity = uPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [uPlus, uMinus, sheetParity, Matrix.mul_apply, Fin.sum_univ_two]

theorem uMinus_mul_sheetParity : uMinus * sheetParity = -uMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [uPlus, uMinus, sheetParity, Matrix.mul_apply, Fin.sum_univ_two]

theorem positive_sheet_cube :
    positiveSheet * sixthRootLift ^ 3 = positiveSheet := by
  rw [sixthRootLift_cube, positiveSheet, liftedParity, kronecker_mul,
    uPlus_mul_sheetParity]
  simp

theorem negative_sheet_cube :
    negativeSheet * sixthRootLift ^ 3 = -negativeSheet := by
  rw [sixthRootLift_cube, negativeSheet, liftedParity, kronecker_mul,
    uMinus_mul_sheetParity]
  simpa using (Matrix.smul_kronecker (-1 : ℂ) uMinus (1 : Mat3C))

end InfoGeometry.Canonical.TomitaTwoSheetThreeColorBridge
