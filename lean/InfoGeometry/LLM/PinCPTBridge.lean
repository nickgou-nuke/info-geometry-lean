import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic

namespace InfoGeometry.LLM.PinCPTBridge

section RingCore

universe u

variable {A : Type u} [Ring A]

/-- Commutator in an associative ring. -/
def commutator (X Y : A) : A := X * Y - Y * X

/-- Anticommutator in an associative ring. -/
def anticommutator (X Y : A) : A := X * Y + Y * X

/--
Minimal Pin-like action for CPT-style orientation-reversing conjugation:
`gamma` is involutive (`gamma^2 = 1`).
-/
structure PinAction where
  gamma : A
  involutive : gamma * gamma = 1

namespace PinAction

/-- Conjugation by `gamma`. -/
def conjugate (P : PinAction (A := A)) (X : A) : A :=
  P.gamma * X * P.gamma

/-- Odd sector condition under `gamma`. -/
def IsOdd (P : PinAction (A := A)) (Q : A) : Prop :=
  P.gamma * Q = -(Q * P.gamma)

/-- Even sector condition under `gamma`. -/
def IsEven (P : PinAction (A := A)) (H : A) : Prop :=
  P.gamma * H = H * P.gamma

/--
Oddness implies evenness of the square:
if `gamma * Q = -(Q * gamma)`, then `gamma * Q² = Q² * gamma`.
-/
@[rep_depth transport]
theorem odd_implies_even_square (P : PinAction (A := A)) {Q : A} (hOdd : IsOdd P Q) :
    IsEven P (Q * Q) := by
  unfold IsOdd IsEven at *
  calc
    P.gamma * (Q * Q) = (P.gamma * Q) * Q := by simp [mul_assoc]
    _ = (-(Q * P.gamma)) * Q := by rw [hOdd]
    _ = -((Q * P.gamma) * Q) := by simp
    _ = -(Q * (P.gamma * Q)) := by simp [mul_assoc]
    _ = -(Q * (-(Q * P.gamma))) := by rw [hOdd]
    _ = Q * (Q * P.gamma) := by simp
    _ = (Q * Q) * P.gamma := by simp [mul_assoc]

/--
Under involutive `gamma`, odd elements flip sign under conjugation.
-/
@[rep_depth transport]
theorem conjugate_odd_eq_neg (P : PinAction (A := A)) {Q : A} (hOdd : IsOdd P Q) :
    conjugate P Q = -Q := by
  unfold conjugate IsOdd at *
  calc
    P.gamma * Q * P.gamma = (-(Q * P.gamma)) * P.gamma := by
      rw [hOdd]
    _ = -(Q * (P.gamma * P.gamma)) := by simp [mul_assoc]
    _ = -(Q * 1) := by simp [P.involutive]
    _ = -Q := by simp

/--
Under involutive `gamma`, the square of an odd element is invariant by conjugation.
-/
@[rep_depth transport]
theorem conjugate_even_square_eq_self (P : PinAction (A := A)) {Q : A} (hOdd : IsOdd P Q) :
    conjugate P (Q * Q) = Q * Q := by
  have hEven : IsEven P (Q * Q) := odd_implies_even_square P hOdd
  unfold conjugate IsEven at *
  calc
    P.gamma * (Q * Q) * P.gamma = ((Q * Q) * P.gamma) * P.gamma := by
      rw [hEven]
    _ = (Q * Q) * (P.gamma * P.gamma) := by simp [mul_assoc]
    _ = (Q * Q) * 1 := by simp [P.involutive]
    _ = Q * Q := by simp

/--
Conjugation by involutive `gamma` is itself involutive.
-/
@[rep_depth transport]
theorem conjugate_involutive (P : PinAction (A := A)) (X : A) :
    conjugate P (conjugate P X) = X := by
  unfold conjugate
  calc
    P.gamma * (P.gamma * X * P.gamma) * P.gamma
        = ((P.gamma * P.gamma) * X) * (P.gamma * P.gamma) := by
            simp [mul_assoc]
    _ = (1 * X) * 1 := by simp [P.involutive]
    _ = X := by simp

/--
Equivalent oddness in anticommutator form.
-/
@[rep_depth transport]
theorem odd_iff_anticommutator_zero (P : PinAction (A := A)) (Q : A) :
    IsOdd P Q ↔ anticommutator P.gamma Q = 0 := by
  unfold IsOdd anticommutator
  constructor
  · intro h
    calc
      P.gamma * Q + Q * P.gamma = (-(Q * P.gamma)) + Q * P.gamma := by rw [h]
      _ = 0 := by simp
  · intro h
    exact eq_neg_of_add_eq_zero_left h

end PinAction

end RingCore

end InfoGeometry.LLM.PinCPTBridge
