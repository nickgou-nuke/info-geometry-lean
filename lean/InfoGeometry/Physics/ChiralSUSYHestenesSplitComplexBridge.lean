import Mathlib.Tactic
import InfoGeometry.Physics.ChiralSUSYBlockFactorization

/-!
# Hestenes split-complex coherence of the finite chiral block

The two canonical unit off-diagonal blocks determine an involutive grading and
an anticommuting real phase axis.  This is only a finite matrix identity.  It
does not identify the auxiliary block with a native Clifford or `KreinSpace`
carrier.
-/

namespace InfoGeometry.Physics

open Matrix

def chiralPhaseAxis {A : Type*} [Ring A] : ChiralBlock A :=
  chiralQMinus (1 : A) - chiralQPlus (1 : A)

theorem chiralUnit_qPlus_anticomm :
    chiralQPlus (1 : ℝ) * chiralQMinus (1 : ℝ) +
        chiralQMinus (1 : ℝ) * chiralQPlus (1 : ℝ) =
      (1 : ChiralBlock ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralQPlus, chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralParity_eq_q_commutator :
    chiralParity =
      chiralQPlus (1 : ℝ) * chiralQMinus (1 : ℝ) -
        chiralQMinus (1 : ℝ) * chiralQPlus (1 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralParity, chiralQPlus, chiralQMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralPhaseAxis_sq :
    chiralPhaseAxis (A := ℝ) * chiralPhaseAxis =
      -(1 : ChiralBlock ℝ) := by
  unfold chiralPhaseAxis
  rw [sub_mul, mul_sub, chiralQMinus_sq, chiralQPlus_sq]
  rw [chiralUnit_qPlus_anticomm]
  ring

theorem chiralPhaseAxis_parity_anticomm :
    chiralPhaseAxis (A := ℝ) * chiralParity +
        chiralParity * chiralPhaseAxis = 0 := by
  unfold chiralPhaseAxis
  rw [chiralParity_qMinus_anticomm, chiralParity_qPlus_anticomm]
  module

theorem chiralParity_sq_coherence :
    chiralParity * chiralParity = (1 : ChiralBlock ℝ) :=
  chiralParity_sq

def chiralHodgeDiracUnit : ChiralBlock ℝ :=
  chiralDirac (1 : ℝ) (1 : ℝ)

theorem chiralHodgeDiracUnit_mul_phaseAxis_eq_parity :
    chiralHodgeDiracUnit * chiralPhaseAxis (A := ℝ) = chiralParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralHodgeDiracUnit, chiralPhaseAxis, chiralDirac,
      chiralQPlus, chiralQMinus, chiralParity, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem chiralPhaseAxis_mul_hodgeDiracUnit_eq_neg_parity :
    chiralPhaseAxis (A := ℝ) * chiralHodgeDiracUnit = -chiralParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralHodgeDiracUnit, chiralPhaseAxis, chiralDirac,
      chiralQPlus, chiralQMinus, chiralParity, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem chiralPhaseAxis_mul_parity_eq_hodgeDiracUnit :
    chiralPhaseAxis (A := ℝ) * chiralParity = chiralHodgeDiracUnit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralHodgeDiracUnit, chiralPhaseAxis, chiralDirac,
      chiralQPlus, chiralQMinus, chiralParity, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem chiralParity_mul_phaseAxis_eq_neg_hodgeDiracUnit :
    chiralParity * chiralPhaseAxis (A := ℝ) = -chiralHodgeDiracUnit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralHodgeDiracUnit, chiralPhaseAxis, chiralDirac,
      chiralQPlus, chiralQMinus, chiralParity, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem chiralPhaseAxis_hodgeDirac_commutator_eq_neg_two_parity :
    chiralPhaseAxis (A := ℝ) * chiralHodgeDiracUnit -
        chiralHodgeDiracUnit * chiralPhaseAxis =
      (-2 : ℝ) • chiralParity := by
  rw [chiralPhaseAxis_mul_hodgeDiracUnit_eq_neg_parity,
    chiralHodgeDiracUnit_mul_phaseAxis_eq_parity]
  module

theorem chiralHodgeDiracUnit_phaseAxis_anticommute :
    chiralHodgeDiracUnit * chiralPhaseAxis (A := ℝ) +
        chiralPhaseAxis * chiralHodgeDiracUnit = 0 := by
  rw [chiralHodgeDiracUnit_mul_phaseAxis_eq_parity,
    chiralPhaseAxis_mul_hodgeDiracUnit_eq_neg_parity]
  simp

theorem chiralParity_hodgeDiracUnit_anticommute :
    chiralParity * chiralHodgeDiracUnit +
        chiralHodgeDiracUnit * chiralParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralHodgeDiracUnit, chiralDirac, chiralParity,
      chiralQPlus, chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralParity_phaseAxis_anticommute_coherence :
    chiralParity * chiralPhaseAxis (A := ℝ) +
        chiralPhaseAxis * chiralParity = 0 :=
  chiralPhaseAxis_parity_anticomm

end InfoGeometry.Physics
