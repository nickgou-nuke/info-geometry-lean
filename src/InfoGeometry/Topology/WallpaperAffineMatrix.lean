import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix
open scoped Matrix

namespace InfoGeometry.Topology

abbrev Affine3 := Matrix (Fin 3) (Fin 3) ℚ

def I3 : Affine3 := 1

def Tx : Affine3 := !![1, 0, 1; 0, 1, 0; 0, 0, 1]
def Ty : Affine3 := !![1, 0, 0; 0, 1, 1; 0, 0, 1]
def TxInv : Affine3 := !![1, 0, -1; 0, 1, 0; 0, 0, 1]
def TyInv : Affine3 := !![1, 0, 0; 0, 1, -1; 0, 0, 1]
def R2 : Affine3 := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]
def Mx : Affine3 := !![1, 0, 0; 0, -1, 0; 0, 0, 1]
def Gx : Affine3 := !![1, 0, (1 / 2 : ℚ); 0, -1, 0; 0, 0, 1]
def GxInv : Affine3 := !![1, 0, (-1 / 2 : ℚ); 0, -1, 0; 0, 0, 1]

theorem p2_square : R2 * R2 = I3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [R2, I3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem p2_conjugation : R2 * Tx * R2 = TxInv := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [R2, Tx, TxInv, Matrix.mul_apply, Fin.sum_univ_three]

theorem pm_square : Mx * Mx = I3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Mx, I3, Matrix.mul_apply, Fin.sum_univ_three]

theorem pm_conjugation : Mx * Ty * Mx = TyInv := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Mx, Ty, TyInv, Matrix.mul_apply, Fin.sum_univ_three]

theorem pg_square : Gx * Gx = Tx := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Gx, Tx, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem pg_inverse : Gx * GxInv = I3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Gx, GxInv, I3, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem pg_conjugation : Gx * Ty * GxInv = TyInv := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Gx, Ty, GxInv, TyInv, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

end InfoGeometry.Topology
