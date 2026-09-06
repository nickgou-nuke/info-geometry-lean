import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

open scoped Matrix

namespace InfoGeometry.Canonical.KleinSixStateBundle

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

abbrev Mat23C := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

def colorReflection : Mat3C := !![(1 : ℂ), 0, 0; 0, 0, 1; 0, 1, 0]

def theta : Mat23C := Matrix.kronecker sheetExchange colorReflection
def triality : Mat23C := Matrix.kronecker sheetParity colorShift

theorem sheetParity_cube : sheetParity ^ 3 = sheetParity := by
  calc
    sheetParity ^ 3 = (sheetParity * sheetParity) * sheetParity := by
      simp [pow_succ]
    _ = sheetParity := by rw [sheetParity_sq]; simp

@[simp] theorem colorReflection_sq : colorReflection ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, colorReflection, Matrix.mul_apply, Fin.sum_univ_three]

theorem colorReflection_shift_colorReflection :
    colorReflection * colorShift * colorReflection = colorShift ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorReflection, colorShift, Matrix.mul_apply, Fin.sum_univ_three,
      pow_two]

theorem theta_sq : theta ^ 2 = 1 := by
  calc
    theta ^ 2 =
        Matrix.kronecker (sheetExchange * sheetExchange)
          (colorReflection * colorReflection) := by
            simpa [theta, pow_two] using
              kronecker_mul sheetExchange sheetExchange colorReflection colorReflection
    _ = 1 := by
      rw [sheetExchange_sq,
        show colorReflection * colorReflection = 1 by
          simpa [pow_two] using colorReflection_sq]
      simp

theorem triality_fifth_formula :
    triality ^ 5 = Matrix.kronecker sheetParity (colorShift ^ 2) := by
  calc
    triality ^ 5 = triality ^ 3 * triality ^ 2 := by
      rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add]
    _ = Matrix.kronecker (sheetParity ^ 3) (colorShift ^ 3) *
        Matrix.kronecker (sheetParity ^ 2) (colorShift ^ 2) := by
      rw [triality, kronecker_pow_three, kronecker_pow_two]
    _ = Matrix.kronecker sheetParity (colorShift ^ 2) := by
      rw [show sheetParity ^ 3 = sheetParity by
        exact sheetParity_cube,
        colorShift_cubed,
        show sheetParity ^ 2 = 1 by rw [pow_two, sheetParity_sq]]
      simpa using kronecker_mul sheetParity 1 (1 : Mat3C) (colorShift ^ 2)

theorem theta_triality_theta :
    theta * triality * theta = -triality ^ 5 := by
  calc
    theta * triality * theta =
        Matrix.kronecker
          (sheetExchange * sheetParity * sheetExchange)
          (colorReflection * colorShift * colorReflection) := by
            simp only [theta, triality]
            rw [kronecker_mul, kronecker_mul]
    _ = Matrix.kronecker (-sheetParity) (colorShift ^ 2) := by
      rw [sheetExchange_parity_sheetExchange,
        colorReflection_shift_colorReflection]
    _ = -triality ^ 5 := by
      rw [triality_fifth_formula]
      simpa using (Matrix.smul_kronecker (-1 : ℂ) sheetParity (colorShift ^ 2))

end InfoGeometry.Canonical.KleinSixStateBundle
