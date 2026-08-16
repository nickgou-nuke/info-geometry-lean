import Mathlib.Tactic
import InfoGeometry.Physics.ChiralSUSYBlockFactorization

/-!
# Cartan weights for the finite chiral block calculus

This file separates the auxiliary two-sector grading from any intrinsic
Clifford or Hestenes grading.  It records the algebraic Cartan commutators of
the off-diagonal nilpotent channels and the commuting action of their even
anticommutator.
-/

namespace InfoGeometry.Physics

open Matrix

theorem chiralParity_qPlus_commutator {A : Type*} [Ring A] (a : A) :
    chiralParity * chiralQPlus a - chiralQPlus a * chiralParity =
      (2 : A) • chiralQPlus a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralParity, chiralQPlus, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

theorem chiralParity_qMinus_commutator {A : Type*} [Ring A] (b : A) :
    chiralParity * chiralQMinus b - chiralQMinus b * chiralParity =
      (-2 : A) • chiralQMinus b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralParity, chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

theorem chiralSUSYHamiltonian_qPlus_commute {A : Type*} [Ring A]
    (a b : A) :
    chiralSUSYHamiltonian a b * chiralQPlus a =
      chiralQPlus a * chiralSUSYHamiltonian a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralSUSYHamiltonian, chiralQPlus, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> noncomm_ring

theorem chiralSUSYHamiltonian_qMinus_commute {A : Type*} [Ring A]
    (a b : A) :
    chiralSUSYHamiltonian a b * chiralQMinus b =
      chiralQMinus b * chiralSUSYHamiltonian a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralSUSYHamiltonian, chiralQMinus, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> noncomm_ring

theorem chiralParity_hamiltonian_commute {A : Type*} [Ring A]
    (a b : A) :
    chiralParity * chiralSUSYHamiltonian a b =
      chiralSUSYHamiltonian a b * chiralParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralParity, chiralSUSYHamiltonian, chiralQPlus,
      chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

end InfoGeometry.Physics
