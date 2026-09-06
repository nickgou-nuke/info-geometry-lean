import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace InfoGeometry.Physics

variable {R : Type*} [CommRing R]

/-- The nilpotent shear operator in the LogCFT Jordan Block. -/
def N_log : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- The scaling operator L_0 for a weight h. -/
def L0 (h : R) : Matrix (Fin 2) (Fin 2) R := h • 1 + N_log

/-- N_log is strictly nilpotent. -/
theorem N_log_sq_zero : N_log * N_log = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [N_log, Matrix.mul_apply, Fin.sum_univ_two]

/-- The explicit matrix form of L_0 is the standard Jordan block. -/
theorem L0_is_jordan_block (h : R) : L0 h = !![h, 1; 0, h] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L0, N_log, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]

end InfoGeometry.Physics
