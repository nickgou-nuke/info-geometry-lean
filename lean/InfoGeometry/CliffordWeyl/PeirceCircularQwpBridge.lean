import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.CliffordWeyl.CircularPauliPeirceBridge

/-!
# Peirce-to-circular basis change by a quarter-wave plate

The unitary `Uqwp = (I - i σ₁) / √2` rotates the Peirce `σ₃` grading into
the circular `σ₂` grading. With the repository convention
`clockwiseProjector = (I + σ₂) / 2`, the left Peirce projector maps to the
clockwise projector and the right Peirce projector maps to the
counterclockwise projector. This is the quarter-wave rotation; it is distinct
from the reflection-like ansatz `(σ₁ + σ₂) / √2`.
-/

noncomputable section

namespace InfoGeometry.CliffordWeyl.PeirceCircularQwpBridge

open InfoGeometry.CliffordWeyl.CircularPauliPeirceBridge
open Matrix

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

def sigma1 : Mat2C := !![(0 : ℂ), 1; 1, 0]
def sigma2 : Mat2C := !![(0 : ℂ), -Complex.I; Complex.I, 0]
def sigma3 : Mat2C := !![(1 : ℂ), 0; 0, -1]

def s2 : ℂ := (Real.sqrt 2 : ℂ) * (1 / 2 : ℂ)

theorem s2_sq : s2 ^ 2 = (1 / 2 : ℂ) := by
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num))
  rw [s2, mul_pow, hsqrt]
  norm_num

@[simp] theorem s2_mul_s2 : s2 * s2 = (1 / 2 : ℂ) := by
  simpa [pow_two] using s2_sq

@[simp] theorem conj_s2 : (starRingEnd ℂ) s2 = s2 := by
  simp [s2]
  change (starRingEnd ℂ) (2 : ℂ) = 2
  exact map_ofNat (starRingEnd ℂ) 2

def Uqwp : Mat2C := !![s2, -Complex.I * s2; -Complex.I * s2, s2]

def Pleft : Mat2C := !![(1 : ℂ), 0; 0, 0]
def Pright : Mat2C := !![(0 : ℂ), 0; 0, 1]

theorem Uqwp_unitary : Uqwpᴴ * Uqwp = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uqwp, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      conj_s2, Complex.conj_I]
  all_goals ring_nf
  all_goals rw [s2_sq]
  all_goals (try rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]])
  all_goals ring

theorem Uqwp_conj_sigma3 : Uqwpᴴ * sigma3 * Uqwp = sigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uqwp, sigma2, sigma3, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, conj_s2, Complex.conj_I]
  all_goals ring_nf
  all_goals rw [s2_sq]
  all_goals (try rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]])
  all_goals ring

theorem Pleft_to_clockwise : Uqwpᴴ * Pleft * Uqwp = clockwiseProjector := by
  rw [clockwiseProjector_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uqwp, Pleft, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, conj_s2, Complex.conj_I]
  all_goals ring_nf
  all_goals rw [s2_sq]
  all_goals (try rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]])
  all_goals ring

theorem Pright_to_counterclockwise :
    Uqwpᴴ * Pright * Uqwp = counterclockwiseProjector := by
  rw [counterclockwiseProjector_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uqwp, Pright, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, conj_s2, Complex.conj_I]
  all_goals ring_nf
  all_goals rw [s2_sq]
  all_goals (try rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]])
  all_goals ring

end InfoGeometry.CliffordWeyl.PeirceCircularQwpBridge

end
