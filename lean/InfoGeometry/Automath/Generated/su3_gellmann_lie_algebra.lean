import Mathlib
import InfoGeometry.Algebra.Cl11Fermions
import InfoGeometry.Algebra.GellMannBasis

/-!
# Clifford Indexing Resolution: Cl(1,1) Gell-Mann SU(3) Bridge

This module formalizes the exact algebraic relations embedding the Clifford algebra
`Cl(1,1)` generators into the `𝔰𝔲(3)` Lie algebra (Gell-Mann basis).
-/

namespace Automath.Generated

noncomputable section

/-- Clifford Cl(1,1) generator E0 embedded into 3x3 complex matrices. -/
def E0 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- Clifford Cl(1,1) generator E1 embedded into 3x3 complex matrices. -/
def E1 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -1, 0; 1, 0, 0; 0, 0, 0]

/-- Projector onto the first two components. -/
def P : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 0]

/-- E0 squares to P. -/
theorem E0_sq : E0 * E0 = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, P, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]

/-- E1 squares to -P. -/
theorem E1_sq : E1 * E1 = -P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, P, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]

/-- E0 and E1 anticommute. -/
theorem E0_E1_anticomm : E0 * E1 + E1 * E0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, E1, Matrix.of_apply]

/-- E0 is related to the gellMann1 basis element. -/
theorem E0_gellMann :
    E0 =
      -Complex.I •
        (InfoGeometry.Algebra.GellMann.gellMann1 :
          Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, InfoGeometry.Algebra.GellMann.gellMann1,
      Matrix.smul_apply, Matrix.of_apply, Complex.I_mul_I]

/-- E1 is related to the gellMann2 basis element. -/
theorem E1_gellMann :
    E1 =
      (InfoGeometry.Algebra.GellMann.gellMann2 :
        Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, InfoGeometry.Algebra.GellMann.gellMann2, Matrix.of_apply]

end

end Automath.Generated
