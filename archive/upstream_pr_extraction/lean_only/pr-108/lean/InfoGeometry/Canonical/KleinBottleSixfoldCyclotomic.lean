import InfoGeometry.Canonical.TomitaTwoSheetThreeColorBridge

/-!
# Finite Klein/glide and cyclotomic reconciliation

This file records the finite algebraic part of the Klein-glide picture.  The
affine glide is proved separately from the fibre reflection, and the latter
is proved on the native three-colour matrices.  No quotient topology or
Hamiltonian descent is asserted here.
-/

open scoped Matrix

namespace InfoGeometry.Canonical.KleinBottleSixfoldCyclotomic

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.TomitaTwoSheetThreeColorBridge

abbrev AffinePoint := ℝ × ℝ

def longitudinalTranslation (p : AffinePoint) : AffinePoint := (p.1 + 2, p.2)

def glide (p : AffinePoint) : AffinePoint := (p.1 + 1, -p.2)

theorem glide_square_eq_translation (p : AffinePoint) :
    glide (glide p) = longitudinalTranslation p := by
  rcases p with ⟨x, y⟩
  simp [glide, longitudinalTranslation]
  ring

def colorReflection : Mat3C := !![(1 : ℂ), 0, 0; 0, 0, 1; 0, 1, 0]

@[simp] theorem colorReflection_sq : colorReflection ^ 2 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pow_two, colorReflection, Matrix.mul_apply, Fin.sum_univ_three]

theorem colorReflection_conjugates_shift :
    colorReflection * colorShift * colorReflection = colorShift ^ 2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [colorReflection, colorShift, Matrix.mul_apply, Fin.sum_univ_three,
      pow_two]

theorem sixthRoot_cube_eq_liftedParity :
    sixthRootLift ^ 3 = liftedParity :=
  sixthRootLift_cube

theorem sixthRoot_sixth_eq_one :
    sixthRootLift ^ 6 = 1 :=
  sixthRootLift_sixth

theorem positive_sheet_triality :
    positiveSheet * sixthRootLift ^ 3 = positiveSheet :=
  positive_sheet_cube

theorem negative_sheet_projective_triality :
    negativeSheet * sixthRootLift ^ 3 = -negativeSheet :=
  negative_sheet_cube

theorem sheet_reflection_anticommutes_with_parity :
    sheetExchange * sheetParity = -(sheetParity * sheetExchange) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sheetExchange, sheetParity, uPlus, uMinus, Matrix.mul_apply,
      Fin.sum_univ_two]

end InfoGeometry.Canonical.KleinBottleSixfoldCyclotomic
