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
    simp [chiralParity, chiralQPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralParity_qMinus_commutator {A : Type*} [Ring A] (b : A) :
    chiralParity * chiralQMinus b - chiralQMinus b * chiralParity =
      (-2 : A) • chiralQMinus b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralParity, chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralSUSYHamiltonian_qPlus_commute {A : Type*} [Ring A]
    (a b : A) :
    chiralSUSYHamiltonian a b * chiralQPlus a =
      chiralQPlus a * chiralSUSYHamiltonian a b := by
  unfold chiralSUSYHamiltonian
  have hq : chiralQPlus a * chiralQPlus a = 0 := chiralQPlus_sq a
  noncomm_ring

theorem chiralSUSYHamiltonian_qMinus_commute {A : Type*} [Ring A]
    (a b : A) :
    chiralSUSYHamiltonian a b * chiralQMinus b =
      chiralQMinus b * chiralSUSYHamiltonian a b := by
  unfold chiralSUSYHamiltonian
  have hq : chiralQMinus b * chiralQMinus b = 0 := chiralQMinus_sq b
  noncomm_ring

theorem chiralParity_hamiltonian_commute {A : Type*} [Ring A]
    (a b : A) :
    chiralParity * chiralSUSYHamiltonian a b =
      chiralSUSYHamiltonian a b * chiralParity := by
  unfold chiralSUSYHamiltonian
  have hp := chiralParity_qPlus_anticomm (A := A) a
  have hm := chiralParity_qMinus_anticomm (A := A) b
  noncomm_ring

end InfoGeometry.Physics
