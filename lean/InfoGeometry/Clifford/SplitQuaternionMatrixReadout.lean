import InfoGeometry.Clifford.Soldering
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The real `2 × 2` split-quaternion readout

This file is an adapter over the existing real Pauli matrices in `Soldering`.
The convention here is the one used by the quaternionic doubling dictionary:
`i² = -1`, `ℓ² = 1`, and `ℓ * i` is the third diagonal Pauli matrix.
It is associative because the readout lands in `M₂(ℝ)`; it is only the
four-dimensional split-quaternion slice, not the full nonassociative Zorn
algebra.
-/

open scoped Matrix

namespace InfoGeometry.Clifford.SplitQuaternionMatrixReadout

open InfoGeometry.Clifford.Soldering

abbrev Mat2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

def one : Mat2R := sigma0

def i : Mat2R := -epsilon

def ell : Mat2R := sigma1

def ellI : Mat2R := sigma3

def coord (a b c d : ℝ) : Mat2R :=
  a • one + b • i + c • ell + d • ellI

@[simp] theorem one_eq_sigma0 : one = sigma0 := rfl

@[simp] theorem i_sq : i * i = -one := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [i, one, epsilon, sigma0, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem ell_sq : ell * ell = one := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [ell, one, sigma1, sigma0, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem ellI_sq : ellI * ellI = one := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [ellI, one, sigma3, sigma0, Matrix.mul_apply, Fin.sum_univ_two]

theorem i_mul_ell : i * ell = -ellI := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [i, ell, ellI, epsilon, sigma1, sigma3,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem ell_mul_i : ell * i = ellI := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [i, ell, ellI, epsilon, sigma1, sigma3,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem i_anticomm_ell : i * ell = -(ell * i) := by
  rw [i_mul_ell, ell_mul_i]

theorem i_anticomm_ellI : i * ellI = -(ellI * i) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [i, ellI, epsilon, sigma3, Matrix.mul_apply, Fin.sum_univ_two]

theorem ell_anticomm_ellI : ell * ellI = -(ellI * ell) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [ell, ellI, sigma1, sigma3, Matrix.mul_apply, Fin.sum_univ_two]

theorem self_anticommutators :
    i * i + i * i = -(2 : ℝ) • one ∧
    ell * ell + ell * ell = (2 : ℝ) • one ∧
    ellI * ellI + ellI * ellI = (2 : ℝ) • one := by
  rw [i_sq, ell_sq, ellI_sq]
  constructor
  · ext r s
    fin_cases r <;> fin_cases s <;> norm_num [one, sigma0]
  constructor <;> ext r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [one, sigma0, Matrix.smul_apply]

theorem commutator_i_ell : i * ell - ell * i = -(2 : ℝ) • ellI := by
  rw [i_mul_ell, ell_mul_i]
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [ellI, sigma3, Matrix.smul_apply]

theorem commutator_ell_ellI : ell * ellI - ellI * ell = (2 : ℝ) • i := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [i, ell, ellI, epsilon, sigma1, sigma3,
      Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

theorem commutator_ellI_i : ellI * i - i * ellI = -(2 : ℝ) • ell := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    norm_num [i, ell, ellI, epsilon, sigma1, sigma3,
      Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

@[simp] theorem coord_apply (a b c d : ℝ) :
    coord a b c d = !![a + d, c - b; c + b, a - d] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [coord, one, i, ell, ellI, sigma0, epsilon, sigma1, sigma3,
      Matrix.add_apply] <;> ring

theorem det_coord (a b c d : ℝ) :
    (coord a b c d).det = a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2 := by
  rw [coord_apply]
  simp [Matrix.det_fin_two]
  ring

theorem coordinate_span (A : Mat2R) :
    ∃ a b c d : ℝ, A = coord a b c d := by
  refine ⟨(A 0 0 + A 1 1) / 2,
    (A 1 0 - A 0 1) / 2,
    (A 0 1 + A 1 0) / 2,
    (A 0 0 - A 1 1) / 2, ?_⟩
  rw [coord_apply]
  ext r s
  fin_cases r <;> fin_cases s <;> simp <;> ring

end InfoGeometry.Clifford.SplitQuaternionMatrixReadout
