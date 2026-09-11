import InfoGeometry.Canonical.ChiralStokesPauliBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChiralStokesPauliBasis

open scoped Matrix

theorem sheetIdentity_sq :
    sheetIdentity * sheetIdentity = sheetIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetIdentity, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetParity_sq :
    sheetParity * sheetParity = sheetIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, sheetIdentity, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetFlip_sq :
    sheetFlip * sheetFlip = sheetIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetIdentity, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetPhase_sq :
    sheetPhase * sheetPhase = sheetIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetPhase, sheetIdentity, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_sq]

theorem sheetParity_sheetFlip_anticommute :
    sheetParity * sheetFlip = -(sheetFlip * sheetParity) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetParity, sheetFlip, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetParity_conjugates_sheetFlip :
    sheetParity * sheetFlip * sheetParity = -sheetFlip := by
  calc
    sheetParity * sheetFlip * sheetParity =
        (sheetParity * sheetFlip) * sheetParity := by
          rw [Matrix.mul_assoc]
    _ = (-(sheetFlip * sheetParity)) * sheetParity := by
          rw [sheetParity_sheetFlip_anticommute]
    _ = -sheetFlip := by
          rw [← neg_mul, Matrix.mul_assoc, sheetParity_sq]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [sheetIdentity, sheetFlip, Matrix.mul_apply,
              Fin.sum_univ_two]

theorem sheetPhase_eq_neg_i_parity_flip :
    sheetPhase = (-Complex.I) • (sheetParity * sheetFlip) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetPhase, sheetParity, sheetFlip, Matrix.mul_apply,
      Fin.sum_univ_two]

end InfoGeometry.Canonical.ChiralStokesPauliBasis
