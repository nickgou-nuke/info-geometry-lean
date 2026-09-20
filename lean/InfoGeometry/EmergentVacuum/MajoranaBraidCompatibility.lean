import InfoGeometry.Canonical.MajoranaBraidingCliffordBridge
import InfoGeometry.Canonical.KreinDoubledCartanPeirceBridge
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

noncomputable section

namespace InfoGeometry.EmergentVacuum.MajoranaBraidCompatibility

open MajoranaBraidingCliffordBridge
open InfoGeometry.Canonical.KreinDoubledCartanPeirce

theorem mat2Mul_eq_native (left right : Matrix (Fin 2) (Fin 2) ℂ) :
    mat2Mul left right = left * right := by
  ext row column
  simp [mat2Mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem majorana_product_eq_complex_grading :
    majoranaProduct12 = Complex.I • eta (R := ℂ) := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [majoranaProduct12, mat2Diag, eta]

theorem braid_commutes_with_grading : Commute majoranaBraidR12 (eta (R := ℂ)) := by
  change majoranaBraidR12 * eta = eta * majoranaBraidR12
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [majoranaBraidR12, mat2Diag, eta, Matrix.mul_apply, Fin.sum_univ_two]

theorem braid_fourth_power : majoranaBraidR12 ^ 4 = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have fourth := majorana_braid_r12_pow4_eq
  simp only [mat2Mul_eq_native] at fourth
  have diagonal : mat2Diag (-1) (-1) = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [mat2Diag]
  simpa only [pow_succ, pow_zero, one_mul, diagonal] using fourth

theorem braid_eighth_power : majoranaBraidR12 ^ 8 = 1 := by
  calc
    majoranaBraidR12 ^ 8 = (majoranaBraidR12 ^ 4) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [braid_fourth_power]; simp

end InfoGeometry.EmergentVacuum.MajoranaBraidCompatibility
