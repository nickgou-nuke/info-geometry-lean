import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics

open Matrix

abbrev ChiralBlock (A : Type*) := Matrix (Fin 2) (Fin 2) A

def chiralQPlus {A : Type*} [Ring A] (a : A) : ChiralBlock A :=
  !![0, a; 0, 0]

def chiralQMinus {A : Type*} [Ring A] (b : A) : ChiralBlock A :=
  !![0, 0; b, 0]

def chiralParity {A : Type*} [Ring A] : ChiralBlock A :=
  !![1, 0; 0, -1]

def chiralDirac {A : Type*} [Ring A] (a b : A) : ChiralBlock A :=
  chiralQPlus a + chiralQMinus b

def chiralSUSYHamiltonian {A : Type*} [Ring A] (a b : A) : ChiralBlock A :=
  chiralQPlus a * chiralQMinus b + chiralQMinus b * chiralQPlus a

theorem chiralQPlus_sq {A : Type*} [Ring A] (a : A) :
    chiralQPlus a * chiralQPlus a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralQPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralQMinus_sq {A : Type*} [Ring A] (b : A) :
    chiralQMinus b * chiralQMinus b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralParity_qPlus_anticomm {A : Type*} [Ring A] (a : A) :
    chiralParity * chiralQPlus a + chiralQPlus a * chiralParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralParity, chiralQPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralParity_qMinus_anticomm {A : Type*} [Ring A] (b : A) :
    chiralParity * chiralQMinus b + chiralQMinus b * chiralParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralParity, chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralDirac_sq_eq_susyHamiltonian {A : Type*} [Ring A] (a b : A) :
    chiralDirac a b * chiralDirac a b = chiralSUSYHamiltonian a b := by
  simp only [chiralDirac, add_mul, mul_add, chiralQPlus_sq a, chiralQMinus_sq b,
    zero_add, add_zero, chiralSUSYHamiltonian]
  rw [add_comm]

theorem chiralParity_sq {A : Type*} [Ring A] :
    chiralParity * chiralParity = (1 : ChiralBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralParity, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Physics
