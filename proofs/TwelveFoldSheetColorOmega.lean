import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import proofs.KleinBottleSixfoldCyclotomic

/-!
# Twelvefold sheet--colour lift

The quartic sheet phase and the cubic colour shift commute because they act
on separate tensor factors.  Their common order-two power is sheet parity.
-/

noncomputable section
namespace TwelveFoldSheetColorOmega

open TwoSheetThreeColorWeyl

/-- The quarter-phase whose square is sheet parity. -/
def omegaSheet : M2C := sheetPlus + Complex.I • sheetMinus

/-- The sheet phase and colour shift on the six-state carrier. -/
def omegaSheetSix : M6C := tensor omegaSheet (1 : M3C)
def colorShiftSix : M6C := tensor (1 : M2C) colorShift

def triality : M6C := sixfoldTriality

/-- A generator of the common `C₁₂` lift. -/
def masterTwelve : M6C := omegaSheetSix ^ 3 * colorShiftSix ^ 2

theorem omegaSheet_sq : omegaSheet ^ 2 = sheetGamma := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaSheet, sheetPlus, sheetMinus, sheetGamma, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem omegaSheet_four : omegaSheet ^ 4 = (1 : M2C) := by
  rw [show (4 : Nat) = 2 + 2 by norm_num, pow_add, omegaSheet_sq,
    sheet_parity.1]

theorem tensor_pow (A : M2C) (B : M3C) (n : Nat) :
    tensor A B ^ n = tensor (A ^ n) (B ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ, ih, tensor_mul]

theorem omegaSheetSix_sq : omegaSheetSix ^ 2 = tensor sheetGamma (1 : M3C) := by
  simp [omegaSheetSix, tensor_pow, omegaSheet_sq]

theorem omegaSheetSix_four : omegaSheetSix ^ 4 = (1 : M6C) := by
  simp [omegaSheetSix, tensor_pow, omegaSheet_four]
theorem colorShift_cube : colorShift ^ 3 = (1 : M3C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [colorShift, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem colorShiftSix_cube : colorShiftSix ^ 3 = (1 : M6C) := by
  simp [colorShiftSix, tensor_pow, colorShift_cube]

theorem masterTwelve_tensor_formula :
    masterTwelve = tensor (omegaSheet ^ 3) (colorShift ^ 2) := by
  simp [masterTwelve, omegaSheetSix, colorShiftSix, tensor_pow, tensor_mul]

private theorem omegaSheet_pow_six : omegaSheet ^ 6 = sheetGamma := by
  rw [show (6 : Nat) = 4 + 2 by norm_num, pow_add, omegaSheet_four,
    omegaSheet_sq, one_mul]

private theorem omegaSheet_pow_nine : omegaSheet ^ 9 = omegaSheet := by
  rw [show (9 : Nat) = 8 + 1 by norm_num, pow_add,
    show omegaSheet ^ 8 = (1 : M2C) by
      rw [show (8 : Nat) = 4 + 4 by norm_num, pow_add, omegaSheet_four,
        one_mul], pow_one, one_mul]

private theorem colorShift_pow_four : colorShift ^ 4 = colorShift := by
  rw [show (4 : Nat) = 3 + 1 by norm_num, pow_add, colorShift_cube,
    pow_one, one_mul]

private theorem colorShift_pow_six : colorShift ^ 6 = (1 : M3C) := by
  rw [show (6 : Nat) = 3 + 3 by norm_num, pow_add, colorShift_cube, one_mul]

theorem masterTwelve_sq : masterTwelve ^ 2 = sixfoldTriality := by
  rw [masterTwelve_tensor_formula, tensor_pow]
  simp only [← pow_mul]
  rw [show 3 * 2 = 6 by norm_num, show 2 * 2 = 4 by norm_num,
    omegaSheet_pow_six, colorShift_pow_four]
  rfl

theorem masterTwelve_cube : masterTwelve ^ 3 = omegaSheetSix := by
  rw [masterTwelve_tensor_formula, tensor_pow]
  simp only [← pow_mul]
  rw [show 3 * 3 = 9 by norm_num, show 2 * 3 = 6 by norm_num,
    omegaSheet_pow_nine, colorShift_pow_six]
  rfl

theorem masterTwelve_six :
    masterTwelve ^ 6 = tensor sheetGamma (1 : M3C) := by
  rw [show (6 : Nat) = 3 + 3 by norm_num, pow_add, masterTwelve_cube]
  simpa [pow_two] using omegaSheetSix_sq

theorem masterTwelve_eight : masterTwelve ^ 8 = colorShiftSix := by
  rw [show (8 : Nat) = 2 + 6 by norm_num, pow_add, masterTwelve_sq,
    masterTwelve_six]
  simp [sixfoldTriality, colorShiftSix, tensor_mul, sheet_parity.1]

theorem masterTwelve_twelve : masterTwelve ^ 12 = (1 : M6C) := by
  rw [show (12 : Nat) = 6 + 6 by norm_num, pow_add, masterTwelve_six,
    tensor_mul, sheet_parity.1]
  simp

theorem masterTwelve_ne_one : masterTwelve ≠ (1 : M6C) := by
  intro h
  have he := congrArg (fun A : M6C => A ⟨0, 0⟩ ⟨0, 1⟩) h
  simp [masterTwelve_tensor_formula, tensor, Matrix.kroneckerMap_apply,
    omegaSheet, sheetPlus, sheetMinus, sheetGamma, colorShift,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
    pow_succ] at he

theorem masterTwelve_sq_ne_one : masterTwelve ^ 2 ≠ (1 : M6C) := by
  rw [masterTwelve_sq]
  intro h
  have he := congrArg (fun A : M6C => A ⟨0, 0⟩ ⟨0, 0⟩) h
  simp [sixfoldTriality, tensor, Matrix.kroneckerMap_apply,
    sheetGamma, sheetPlus, sheetMinus, colorShift] at he

theorem masterTwelve_cube_ne_one : masterTwelve ^ 3 ≠ (1 : M6C) := by
  rw [masterTwelve_cube]
  intro h
  have he := congrArg (fun A : M6C => A ⟨1, 0⟩ ⟨1, 0⟩) h
  simp [omegaSheetSix, tensor, Matrix.kroneckerMap_apply,
    omegaSheet, sheetPlus, sheetMinus] at he
  have him := congrArg Complex.im he
  norm_num at him

theorem masterTwelve_six_ne_one : masterTwelve ^ 6 ≠ (1 : M6C) := by
  rw [masterTwelve_six]
  intro h
  have he := congrArg (fun A : M6C => A ⟨1, 0⟩ ⟨1, 0⟩) h
  simp [tensor, Matrix.kroneckerMap_apply, sheetGamma,
    sheetPlus, sheetMinus] at he
  norm_num at he

 def colorShiftSix_ne_one : colorShiftSix ≠ (1 : M6C) := by
  intro h
  have he := congrArg (fun A : M6C => A ⟨0, 0⟩ ⟨0, 2⟩) h
  simp [colorShiftSix, tensor, Matrix.kroneckerMap_apply,
    colorShift] at he

 theorem masterTwelve_four_ne_one : masterTwelve ^ 4 ≠ (1 : M6C) := by
  intro h
  have h8 : masterTwelve ^ 8 = (1 : M6C) := by
    rw [show (8 : Nat) = 4 + 4 by norm_num, pow_add, h]
    simp
  rw [masterTwelve_eight] at h8
  exact colorShiftSix_ne_one h8

 def HasExactOrder12 (A : M6C) : Prop :=
  A ^ 12 = (1 : M6C) ∧
    A ≠ (1 : M6C) ∧
    A ^ 2 ≠ (1 : M6C) ∧
    A ^ 3 ≠ (1 : M6C) ∧
    A ^ 4 ≠ (1 : M6C) ∧
    A ^ 6 ≠ (1 : M6C)

 theorem masterTwelve_exact_order12 : HasExactOrder12 masterTwelve := by
  exact ⟨masterTwelve_twelve, masterTwelve_ne_one,
    masterTwelve_sq_ne_one, masterTwelve_cube_ne_one,
    masterTwelve_four_ne_one, masterTwelve_six_ne_one⟩

end TwelveFoldSheetColorOmega
end noncomputable section
