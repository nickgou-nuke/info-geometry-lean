import Mathlib.Tactic
import InfoGeometry.Physics.ChiralSUSYBlockFactorization
import InfoGeometry.Physics.ChiralSUSYHestenesSplitComplexBridge

/-!
# Finite relative surprisal on the chiral block

This is the two-sector finite ansatz `𝒦 = κ I + a Γ`.  It records the
Cartan weights of the nilpotent channels without identifying this auxiliary
matrix with a Tomita operator, a relative modular operator, or a native
Clifford/Krein grading.
-/

namespace InfoGeometry.Physics

open Matrix

def chiralRelativeSurprisal (κ a : ℝ) : ChiralBlock ℝ :=
  κ • (1 : ChiralBlock ℝ) + a • chiralParity

def chiralDiracCommutator (X Y : ChiralBlock ℝ) : ChiralBlock ℝ :=
  X * Y - Y * X

def chiralTrace2 (A : ChiralBlock ℝ) : ℝ := A 0 0 + A 1 1

theorem chiralRelativeSurprisal_trace (κ a : ℝ) :
    chiralTrace2 (chiralRelativeSurprisal κ a) = 2 * κ := by
  simp [chiralTrace2, chiralRelativeSurprisal, chiralParity,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  ring

theorem chiralRelativeSurprisal_centered (κ a : ℝ) :
    chiralRelativeSurprisal κ a -
        (chiralTrace2 (chiralRelativeSurprisal κ a) / 2) •
          (1 : ChiralBlock ℝ) = a • chiralParity := by
  rw [chiralRelativeSurprisal_trace]
  unfold chiralRelativeSurprisal
  module

theorem chiralRelativeSurprisal_comm_qPlus (κ a : ℝ) :
    chiralDiracCommutator (chiralRelativeSurprisal κ a)
      (chiralQPlus (1 : ℝ)) =
      (2 * a) • chiralQPlus (1 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiracCommutator, chiralRelativeSurprisal,
      chiralParity, chiralQPlus, Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring

theorem chiralRelativeSurprisal_comm_qMinus (κ a : ℝ) :
    chiralDiracCommutator (chiralRelativeSurprisal κ a)
      (chiralQMinus (1 : ℝ)) =
      (-2 * a) • chiralQMinus (1 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiracCommutator, chiralRelativeSurprisal,
      chiralParity, chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring

theorem chiralPhaseAxis_relativeSurprisal_commutator (κ a : ℝ) :
    chiralPhaseAxis (A := ℝ) * chiralRelativeSurprisal κ a -
        chiralRelativeSurprisal κ a * chiralPhaseAxis =
      (2 * a) • chiralHodgeDiracUnit := by
  unfold chiralRelativeSurprisal
  rw [sub_eq_add_neg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, mul_smul_comm]
  rw [chiralPhaseAxis_mul_parity_eq_hodgeDiracUnit,
    chiralParity_mul_phaseAxis_eq_neg_hodgeDiracUnit]
  simp
  module

end InfoGeometry.Physics
