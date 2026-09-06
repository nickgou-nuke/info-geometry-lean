import Mathlib

open Matrix
open scoped Matrix ComplexOrder

namespace InfoGeometry.OperatorAlgebraicLorentzLift

set_option linter.unusedSectionVars false

-- 1. Weyl Representation Local Clifford Atom
def Gamma_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

def J_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

theorem Gamma_sq : Gamma_matrix ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
  simp [sq, Gamma_matrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_sq : J_matrix ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
  simp [sq, J_matrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem Gamma_J_anti_comm : Gamma_matrix * J_matrix + J_matrix * Gamma_matrix = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
  simp [Gamma_matrix, J_matrix]

-- 2. CAR algebra from Clifford generators (Algebraic)
section WittBasis

variable {A : Type*} [Ring A] [Algebra ℂ A]

def anticomm (x y : A) : A := x * y + y * x

lemma anticomm_symm (x y : A) : anticomm x y = anticomm y x := by
  dsimp [anticomm]
  exact add_comm _ _

lemma anticomm_expand (x1 x2 y1 y2 : A) (c1 c2 d1 d2 : ℂ) :
  anticomm (c1 • x1 + c2 • x2) (d1 • y1 + d2 • y2) =
  (c1 * d1) • anticomm x1 y1 + (c1 * d2) • anticomm x1 y2 +
  (c2 * d1) • anticomm x2 y1 + (c2 * d2) • anticomm x2 y2 := by
  dsimp [anticomm]
  simp only [mul_add, add_mul, smul_add, smul_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  have hc1 : d1 * c1 = c1 * d1 := mul_comm _ _
  have hc2 : d1 * c2 = c2 * d1 := mul_comm _ _
  have hc3 : d2 * c1 = c1 * d2 := mul_comm _ _
  have hc4 : d2 * c2 = c2 * d2 := mul_comm _ _
  rw [hc1, hc2, hc3, hc4]
  abel

variable (gamma1 gamma2 : A)

noncomputable def witt_a : A := (1/2 : ℂ) • gamma1 + (Complex.I/2 : ℂ) • gamma2
noncomputable def witt_c : A := (1/2 : ℂ) • gamma1 + (-Complex.I/2 : ℂ) • gamma2

theorem witt_anticomm_a_c (h1 : anticomm gamma1 gamma1 = 2) (h2 : anticomm gamma2 gamma2 = 2) (h12 : anticomm gamma1 gamma2 = 0) : 
    anticomm (witt_a gamma1 gamma2) (witt_c gamma1 gamma2) = 1 := by
  dsimp [witt_a, witt_c]
  rw [anticomm_expand]
  rw [h1, h2, h12]
  have h21 : anticomm gamma2 gamma1 = 0 := by
    rw [anticomm_symm]
    exact h12
  rw [h21]
  simp only [smul_zero, add_zero]
  have h_add : (1 / 2 * (1 / 2) : ℂ) • (2 : A) + (Complex.I / 2 * (-Complex.I / 2) : ℂ) • (2 : A) = ((1 / 2 * (1 / 2) : ℂ) + (Complex.I / 2 * (-Complex.I / 2) : ℂ)) • (2 : A) := by
    rw [add_smul]
  rw [h_add]
  have h_scalar : (1 / 2 * (1 / 2) : ℂ) + (Complex.I / 2 * (-Complex.I / 2) : ℂ) = (1/2 : ℂ) := by
    ring_nf; rw [Complex.I_sq]; norm_num
  rw [h_scalar]
  have h_two : (1 / 2 : ℂ) • (2 : A) = (1 / 2 : ℂ) • algebraMap ℂ A (2 : ℂ) := by
    congr 1
    exact (map_ofNat (algebraMap ℂ A) 2).symm
  rw [h_two, Algebra.smul_def, ← map_mul]
  have h_mul : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  rw [h_mul]
  exact map_one (algebraMap ℂ A)

theorem witt_anticomm_a_a (h1 : anticomm gamma1 gamma1 = 2) (h2 : anticomm gamma2 gamma2 = 2) (h12 : anticomm gamma1 gamma2 = 0) : 
    anticomm (witt_a gamma1 gamma2) (witt_a gamma1 gamma2) = 0 := by
  dsimp [witt_a]
  rw [anticomm_expand, h1, h2, h12]
  have h21 : anticomm gamma2 gamma1 = 0 := by
    rw [anticomm_symm]; exact h12
  rw [h21]
  simp only [smul_zero, add_zero]
  rw [← add_smul]
  have h_scalar : (1 / 2 * (1 / 2) : ℂ) + (Complex.I / 2 * (Complex.I / 2) : ℂ) = 0 := by
    ring_nf; rw [Complex.I_sq]; norm_num
  rw [h_scalar, zero_smul]

theorem witt_anticomm_c_c (h1 : anticomm gamma1 gamma1 = 2) (h2 : anticomm gamma2 gamma2 = 2) (h12 : anticomm gamma1 gamma2 = 0) : 
    anticomm (witt_c gamma1 gamma2) (witt_c gamma1 gamma2) = 0 := by
  dsimp [witt_c]
  rw [anticomm_expand, h1, h2, h12]
  have h21 : anticomm gamma2 gamma1 = 0 := by
    rw [anticomm_symm]; exact h12
  rw [h21]
  simp only [smul_zero, add_zero]
  rw [← add_smul]
  have h_scalar : (1 / 2 * (1 / 2) : ℂ) + (-Complex.I / 2 * (-Complex.I / 2) : ℂ) = 0 := by
    ring_nf; rw [Complex.I_sq]; norm_num
  rw [h_scalar, zero_smul]

end WittBasis

-- 3. Quadratic Operator Lie Algebra
section QuadraticLie

variable {A : Type*} [Ring A] [Algebra ℂ A]

def commutator (x y : A) : A := x * y - y * x

lemma quadratic_commutator (A_op B C D : A) :
    commutator (A_op * B) (C * D) = 
      A_op * (anticomm B C) * D - A_op * C * (anticomm B D) + (anticomm A_op C) * D * B - C * (anticomm A_op D) * B := by
  dsimp [commutator, anticomm]
  noncomm_ring

end QuadraticLie

end InfoGeometry.OperatorAlgebraicLorentzLift
