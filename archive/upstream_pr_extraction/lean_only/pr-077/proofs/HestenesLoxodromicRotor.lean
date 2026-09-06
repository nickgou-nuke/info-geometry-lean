import proofs.HestenesPhaseBoostRotors

/-!
# Algebraic loxodromic rotor action

This owner composes the certified boost and rotation normal forms and proves
that the circular sheet generators are eigenvectors of the sandwich action.
The scalar constraints needed for a normalized rotor are inherited from the
previous owner.
-/

noncomputable section
namespace HestenesLoxodromicRotor

open TwoSheetThreeColorWeyl
open HestenesCircularSheetCAR
open HestenesPhaseBoostRotors

abbrev Sheet := M2C

def loxodromicRotor (a b c d : ℂ) : Sheet :=
  boostRotor a b * rotationRotor c d

def loxodromicReverse (a b c d : ℂ) : Sheet :=
  rotationReverse c d * boostReverse a b

@[simp] theorem K_cPlus : K * cPlus = cPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [K, cPlus, sheetGamma, sheetPlus, sheetMinus, sheetFlip,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem cPlus_K : cPlus * K = -cPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [K, cPlus, sheetGamma, sheetPlus, sheetMinus, sheetFlip,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem K_cMinus : K * cMinus = -cMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [K, cMinus, sheetGamma, sheetPlus, sheetMinus, sheetFlip,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem cMinus_K : cMinus * K = cMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [K, cMinus, sheetGamma, sheetPlus, sheetMinus, sheetFlip,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem loxodromic_cPlus_action (a b c d : ℂ) :
    loxodromicRotor a b c d * cPlus * loxodromicReverse a b c d =
      ((a + b) * (c + Complex.I * d)) ^ 2 • cPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [loxodromicRotor, loxodromicReverse, boostRotor, boostReverse,
      rotationRotor, rotationReverse, IK, K, cPlus, sheetGamma, sheetPlus,
      sheetMinus, sheetFlip, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

 theorem loxodromic_cMinus_action (a b c d : ℂ) :
    loxodromicRotor a b c d * cMinus * loxodromicReverse a b c d =
      ((a - b) * (c - Complex.I * d)) ^ 2 • cMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [loxodromicRotor, loxodromicReverse, boostRotor, boostReverse,
      rotationRotor, rotationReverse, IK, K, cMinus, sheetGamma, sheetPlus,
      sheetMinus, sheetFlip, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

end HestenesLoxodromicRotor
end noncomputable section
