import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Quaternionic Pauli real form

This file fixes the orientation convention

`i ↦ -I σ₃`, `j ↦ -I σ₂`, `k ↦ I σ₁`.

The sign on the third generator is forced by `ij = k`; it is not an
additional choice once the first two images and the quaternion orientation
have been fixed.  The split-quaternion matrix form is owned separately by
`Clifford.Soldering`.
-/

namespace InfoGeometry.Clifford.QuaternionPauliRealForm

open scoped Matrix

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

def sigma1 : Mat2C := !![(0 : ℂ), 1; 1, 0]

def sigma2 : Mat2C := !![(0 : ℂ), -Complex.I; Complex.I, 0]

def sigma3 : Mat2C := !![(1 : ℂ), 0; 0, -1]

def qi : Mat2C := (-Complex.I) • sigma3

def qj : Mat2C := (-Complex.I) • sigma2

def qk : Mat2C := Complex.I • sigma1

def quaternionPauli (q : ℝ × ℝ × ℝ × ℝ) : Mat2C :=
  (q.1 : ℂ) • (1 : Mat2C) +
    (q.2.1 : ℂ) • qi +
    (q.2.2.1 : ℂ) • qj +
    (q.2.2.2 : ℂ) • qk

@[simp] theorem qi_sq : qi * qi = -(1 : Mat2C) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [qi, sigma3, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

@[simp] theorem qj_sq : qj * qj = -(1 : Mat2C) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [qj, sigma2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

@[simp] theorem qk_sq : qk * qk = -(1 : Mat2C) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [qk, sigma1, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

theorem qi_mul_qj : qi * qj = qk := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [qi, qj, qk, sigma1, sigma2, sigma3, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_sq]

theorem qj_mul_qk : qj * qk = qi := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [qi, qj, qk, sigma1, sigma2, sigma3, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_sq]

theorem qk_mul_qi : qk * qi = qj := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [qi, qj, qk, sigma1, sigma2, sigma3, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_sq]

theorem quaternionPauli_formula (q : ℝ × ℝ × ℝ × ℝ) :
    quaternionPauli q =
      !![(q.1 : ℂ) - (q.2.1 : ℂ) * Complex.I,
        -(q.2.2.1 : ℂ) + (q.2.2.2 : ℂ) * Complex.I;
        (q.2.2.1 : ℂ) + (q.2.2.2 : ℂ) * Complex.I,
        (q.1 : ℂ) + (q.2.1 : ℂ) * Complex.I] := by
  rcases q with ⟨a, b, c, d⟩
  ext r col
  fin_cases r <;> fin_cases col <;>
    simp [quaternionPauli, qi, qj, qk, sigma1, sigma2, sigma3,
      Matrix.one_apply, Matrix.smul_apply] <;> ring

theorem quaternionPauli_det (q : ℝ × ℝ × ℝ × ℝ) :
    (quaternionPauli q).det =
      ((q.1 : ℂ) ^ 2 + (q.2.1 : ℂ) ^ 2 +
        (q.2.2.1 : ℂ) ^ 2 + (q.2.2.2 : ℂ) ^ 2) := by
  rw [quaternionPauli_formula]
  simp [Matrix.det_fin_two, pow_two]
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by
    norm_num [pow_two]
  ring_nf
  rw [hI]
  ring

end InfoGeometry.Clifford.QuaternionPauliRealForm
