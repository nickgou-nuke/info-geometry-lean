import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open Matrix

abbrev Dim8 := Fin 8
abbrev Mat8 := Matrix Dim8 Dim8 ℝ

def eps0 : Mat8 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0]]

theorem eps0_sq : eps0 * eps0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
