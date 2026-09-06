import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.KleinSixStateBundle
import InfoGeometry.Canonical.FiniteKreinTomitaSixState

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.SixStateModularConjugationIdentification

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.KleinSixStateBundle

abbrev SixStateOperator := TwoSheetThreeColorWeyl.Mat23C

def modularConjugation (X : SixStateOperator) : SixStateOperator :=
  KleinSixStateBundle.theta * star X * KleinSixStateBundle.theta

def leftAction (A X : SixStateOperator) : SixStateOperator := A * X

def rightAction (A X : SixStateOperator) : SixStateOperator := X * A

lemma sandwich_mul (h : KleinSixStateBundle.theta *
    KleinSixStateBundle.theta = (1 : SixStateOperator))
    (A B : SixStateOperator) :
    (KleinSixStateBundle.theta * A * KleinSixStateBundle.theta) *
        (KleinSixStateBundle.theta * B * KleinSixStateBundle.theta) =
      KleinSixStateBundle.theta * A * B * KleinSixStateBundle.theta := by
  calc
    (KleinSixStateBundle.theta * A * KleinSixStateBundle.theta) *
        (KleinSixStateBundle.theta * B * KleinSixStateBundle.theta) =
      KleinSixStateBundle.theta * A *
        (KleinSixStateBundle.theta * KleinSixStateBundle.theta) * B *
          KleinSixStateBundle.theta := by
            simp only [Matrix.mul_assoc]
    _ = KleinSixStateBundle.theta * A * B * KleinSixStateBundle.theta := by
          rw [h]
          simp

theorem theta_star : star theta = theta := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;> fin_cases i <;> fin_cases j <;>
    simp [KleinSixStateBundle.theta, colorReflection, sheetExchange,
      Matrix.star_apply, Matrix.kronecker_apply] <;> norm_num

theorem theta_mul_theta :
    KleinSixStateBundle.theta * KleinSixStateBundle.theta =
      (1 : SixStateOperator) := by
  simpa [pow_two] using KleinSixStateBundle.theta_sq

theorem modularConjugation_involutive (X : SixStateOperator) :
    modularConjugation (modularConjugation X) = X := by
  simp only [modularConjugation, Matrix.star_mul, star_star, theta_star]
  calc
    KleinSixStateBundle.theta *
        (KleinSixStateBundle.theta * (X * KleinSixStateBundle.theta)) *
          KleinSixStateBundle.theta =
      (KleinSixStateBundle.theta * KleinSixStateBundle.theta) * X *
        (KleinSixStateBundle.theta * KleinSixStateBundle.theta) := by
          simp only [Matrix.mul_assoc]
    _ = X := by rw [theta_mul_theta]; simp

theorem modularConjugation_leftAction (A X : SixStateOperator) :
    modularConjugation (leftAction A X) =
      rightAction (theta * star A * theta) (modularConjugation X) := by
  simp only [modularConjugation, leftAction, rightAction, Matrix.star_mul,
    theta_star]
  calc
    KleinSixStateBundle.theta * (star X * star A) *
        KleinSixStateBundle.theta =
      KleinSixStateBundle.theta * star X * star A *
        KleinSixStateBundle.theta := by simp only [Matrix.mul_assoc]
    _ = (KleinSixStateBundle.theta * star X * KleinSixStateBundle.theta) *
        (KleinSixStateBundle.theta * star A * KleinSixStateBundle.theta) := by
          symm
          exact sandwich_mul theta_mul_theta (star X) (star A)

theorem modularConjugation_leftAction_eq_rightAction (A X : SixStateOperator) :
    modularConjugation (leftAction A X) =
      rightAction
        (KleinSixStateBundle.theta * star A * KleinSixStateBundle.theta)
        (modularConjugation X) := by
  exact modularConjugation_leftAction A X

theorem theta_parity_theta :
    theta * sixParity * theta = -sixParity := by
  calc
    theta * sixParity * theta =
        Matrix.kronecker
          (sheetExchange * sheetParity * sheetExchange)
          (colorReflection * (1 : Mat3C) * colorReflection) := by
            simp only [KleinSixStateBundle.theta, sixParity]
            rw [kronecker_mul, kronecker_mul]
    _ = Matrix.kronecker (-sheetParity) (1 : Mat3C) := by
          rw [sheetExchange_parity_sheetExchange]
          rw [show colorReflection * (1 : Mat3C) * colorReflection =
            colorReflection * colorReflection by simp]
          congr 1
          simpa [pow_two] using KleinSixStateBundle.colorReflection_sq
    _ = -sixParity := by
          simpa [sixParity] using
            (Matrix.smul_kronecker (-1 : ℂ) sheetParity (1 : Mat3C))

theorem theta_triality_theta_eq_neg_fifth :
    theta * triality * theta = -triality ^ 5 := by
  exact KleinSixStateBundle.theta_triality_theta

end InfoGeometry.Canonical.SixStateModularConjugationIdentification
