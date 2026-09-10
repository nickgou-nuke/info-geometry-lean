import InfoGeometry.Volume.MajoranaPfaffianFour
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Quantum.MajoranaVacuumWickFour

noncomputable section

open InfoGeometry.Volume.MajoranaPfaffianFour
open InfoGeometry.Volume.OrientedPfaffian

abbrev Mat4C := InfoGeometry.Algebra.FiniteSpin.Mat4C

def gamma (i : Fin 4) : Mat4C :=
  match i with
  | 0 => !![0, 0, 1, 0;
            0, 0, 0, 1;
            1, 0, 0, 0;
            0, 1, 0, 0]
  | 1 => !![0, 0, -Complex.I, 0;
            0, 0, 0, -Complex.I;
            Complex.I, 0, 0, 0;
            0, Complex.I, 0, 0]
  | 2 => !![0, 1, 0, 0;
            1, 0, 0, 0;
            0, 0, 0, -1;
            0, 0, -1, 0]
  | 3 => !![0, -Complex.I, 0, 0;
            Complex.I, 0, 0, 0;
            0, 0, 0, Complex.I;
            0, 0, -Complex.I, 0]

/-- The vector state at the first computational basis vector. -/
def vacuumExpectation (A : Mat4C) : ℂ := A 0 0

/-- The standard real covariance extracted from the vector state. -/
def covariance (i j : Fin 4) : ℝ :=
  (Complex.I / 2 *
      (vacuumExpectation (gamma i * gamma j) -
        vacuumExpectation (gamma j * gamma i))).re

def covarianceMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => covariance i j

theorem covarianceMatrix_explicit :
    covarianceMatrix = !![0, -1, 0, 0;
                          1, 0, 0, 0;
                          0, 0, 0, -1;
                          0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covarianceMatrix, covariance, vacuumExpectation, gamma,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

theorem covarianceMatrix_skew :
    Matrix.transpose covarianceMatrix = -covarianceMatrix := by
  rw [covarianceMatrix_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply]

def fourPoint : ℂ :=
  vacuumExpectation (gamma 0 * gamma 1 * gamma 2 * gamma 3)

theorem fourPoint_explicit : fourPoint = -1 := by
  simp [fourPoint, vacuumExpectation, gamma, Matrix.mul_apply,
    Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two,
    Matrix.cons_val_three] <;> norm_num

theorem vacuum_wick_four :
    fourPoint.re =
      -(covariance 0 1) * covariance 2 3 +
        covariance 0 2 * covariance 1 3 -
        covariance 0 3 * covariance 1 2 := by
  rw [fourPoint_explicit]
  have h01 : covariance 0 1 = -1 := by
    norm_num [covariance, vacuumExpectation, gamma, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have h02 : covariance 0 2 = 0 := by
    norm_num [covariance, vacuumExpectation, gamma, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have h03 : covariance 0 3 = 0 := by
    norm_num [covariance, vacuumExpectation, gamma, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have h12 : covariance 1 2 = 0 := by
    norm_num [covariance, vacuumExpectation, gamma, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have h13 : covariance 1 3 = 0 := by
    norm_num [covariance, vacuumExpectation, gamma, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have h23 : covariance 2 3 = -1 := by
    norm_num [covariance, vacuumExpectation, gamma, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three]
  rw [h01, h02, h03, h12, h13, h23]
  norm_num

theorem orientedPfaffian_two_vacuum_wick :
    fourPoint.re =
      -(orientedPfaffian 2
        (skewFourByFour (covariance 0 1) (covariance 0 2)
          (covariance 0 3) (covariance 1 2) (covariance 1 3)
          (covariance 2 3))) := by
  rw [vacuum_wick_four]
  rw [orientedPfaffian_two_eq_majoranaPfaffianFour]
  rw [majoranaPfaffianFour_eq_three_matchings]
  ring

end

end InfoGeometry.Quantum.MajoranaVacuumWickFour
