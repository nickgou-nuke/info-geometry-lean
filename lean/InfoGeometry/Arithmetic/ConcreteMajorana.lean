import InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

noncomputable section

namespace InfoGeometry.Arithmetic.ConcreteMajorana

open Matrix
open InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

/-!
# Concrete two-by-two Clifford readout

This file defines two explicit real `Fin 2` matrices and proves their
multiplication identities. It does not define a Hilbert-space operator or a
general Majorana representation.
-/

/-- Explicit symmetric off-diagonal matrix. -/
def BK_Matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1],
    ![1, 0]]

/-- Explicit diagonal involution. -/
def Rho_Matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0],
    ![0, -1]]

/-- Sum of the two explicit matrices. -/
def CombinedDirac_Matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  BK_Matrix + Rho_Matrix

/-- The off-diagonal matrix squares to the identity. -/
theorem bk_sq_is_id : BK_Matrix * BK_Matrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
    simp [BK_Matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The diagonal matrix squares to the identity. -/
theorem rho_sq_is_id : Rho_Matrix * Rho_Matrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
    simp [Rho_Matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two explicit matrices anticommute. -/
theorem rho_anticommutes_bk : Rho_Matrix * BK_Matrix = - (BK_Matrix * Rho_Matrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
    simp [Rho_Matrix, BK_Matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-- The sum squares to twice the identity matrix. -/
theorem combined_dirac_sq :
  CombinedDirac_Matrix * CombinedDirac_Matrix = 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
    simp [CombinedDirac_Matrix, BK_Matrix, Rho_Matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply] <;> norm_num

/-- Definitional formula for the sum matrix. -/
theorem combined_dirac_formula : CombinedDirac_Matrix = BK_Matrix + Rho_Matrix := rfl

/-- Readout of the square identity. -/
theorem trivial_majorana_dirac_square :
    CombinedDirac_Matrix * CombinedDirac_Matrix =
      2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  combined_dirac_sq

/-- Compatibility readout of the same square identity. -/
theorem modeEnergyCoefficient_zero (_ : Unit) :
    CombinedDirac_Matrix * CombinedDirac_Matrix =
      2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  combined_dirac_sq

end InfoGeometry.Arithmetic.ConcreteMajorana
