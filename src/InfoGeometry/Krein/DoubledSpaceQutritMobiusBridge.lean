import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge
import InfoGeometry.Physics.LogCFT

/-!
# Qutrit Möbius triad on the native doubled carrier

The qutrit-indexed elliptic, parabolic, and hyperbolic generators are the
same real `2 × 2` matrices already represented on `DoubledSpace E` by
`ρclock`.  This owner records that identification without identifying their
conjugacy classes or their flows.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceQutritMobiusBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
open InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R

theorem qutritMobiusOperator_zero_eq_matrixClockAxis :
    qutritMobiusOperator 0 = matrixClockAxis := by
  rfl

theorem qutritMobiusOperator_one_eq_parabolicK :
    qutritMobiusOperator 1 = InfoGeometry.Algebra.HypercomplexTriad.N := by
  rfl

theorem qutritMobiusOperator_one_eq_logCFTGenerator :
    qutritMobiusOperator 1 = InfoGeometry.Algebra.HypercomplexTriad.N := by
  rfl

theorem qutritMobiusOperator_two_eq_matrixEpsilon :
    qutritMobiusOperator 2 = matrixEpsilon := by
  rfl

theorem ρclock_qutrit_elliptic :
    ρclock (E := E) (qutritMobiusOperator 0) =
      clockAxis (E := E) := by
  rw [qutritMobiusOperator_zero_eq_matrixClockAxis]
  exact ρclock_matrixClockAxis

theorem ρclock_qutrit_parabolic :
    ρclock (E := E) (qutritMobiusOperator 1) =
      ρclock (E := E) (InfoGeometry.Algebra.HypercomplexTriad.N) := by
  rw [qutritMobiusOperator_one_eq_parabolicK]

theorem ρclock_qutrit_hyperbolic :
    ρclock (E := E) (qutritMobiusOperator 2) =
      spectral_epsilon (E := E) := by
  rw [qutritMobiusOperator_two_eq_matrixEpsilon]
  exact ρclock_matrixEpsilon

theorem qutrit_triplet_square_readout (i : Fin 3) :
    qutritMobiusOperator i * qutritMobiusOperator i =
      (InfoGeometry.Clifford.OpSquareTriadBridge.opSquareScalar
        (qutritOpSquareClass i)) • (1 : Mat2) :=
  qutritMobiusOperator_sq i

end InfoGeometry.Krein.DoubledSpaceQutritMobiusBridge
