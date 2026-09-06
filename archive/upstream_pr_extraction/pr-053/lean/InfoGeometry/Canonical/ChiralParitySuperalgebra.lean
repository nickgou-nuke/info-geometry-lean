import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorGradedAdjointLift

/-!
# Odd--odd closure in a graded operator ring

This file records the associative-ring identity needed for the odd part of a
graded operator algebra.  It does not introduce a spacetime model or a
central extension.

1. **Odd operators**: `Q` and `Q'` anticommute with the chosen grading `Γ`.
2. **Odd--odd closure**: their anticommutator commutes with `Γ`.
   Centrality is not asserted; it requires additional hypotheses.
-/

variable {A : Type*} [Ring A]
variable (Γ : A)

namespace NoncommutativeGeometry

/-- A Chiral Parity Supercharge is mathematically an Odd operator. -/
class IsChiralSupercharge (Γ Q : A) : Prop where
  is_odd : isOdd Γ Q

/-- The odd--odd anticommutator in the associative operator ring. -/
def anticomm (X Y : A) : A := X * Y + Y * X

/--
The Fundamental Theorem of the Lie Superalgebra:
The anticommutator of any two supercharges (Odd) is necessarily a bosonic (Even) operator.
-/
theorem superalgebra_closure (Q Q' : A)
    [hQ : IsChiralSupercharge Γ Q] [hQ' : IsChiralSupercharge Γ Q'] :
    isEven Γ (anticomm Q Q') := by
  unfold anticomm isEven
  -- `isOdd` gives Γ * Q = -(Q * Γ), and similarly for Q'.
  have h1 : Γ * Q = - (Q * Γ) := by
    calc
      Γ * Q = Γ * Q + Q * Γ - Q * Γ := by rw [add_sub_cancel_right]
      _ = 0 - Q * Γ := by rw [hQ.is_odd]
      _ = - (Q * Γ) := by rw [zero_sub]

  have h2 : Γ * Q' = - (Q' * Γ) := by
    calc
      Γ * Q' = Γ * Q' + Q' * Γ - Q' * Γ := by rw [add_sub_cancel_right]
      _ = 0 - Q' * Γ := by rw [hQ'.is_odd]
      _ = - (Q' * Γ) := by rw [zero_sub]

  calc
    Γ * (Q * Q' + Q' * Q)
      = Γ * (Q * Q') + Γ * (Q' * Q) := mul_add Γ (Q * Q') (Q' * Q)
    _ = (Γ * Q) * Q' + (Γ * Q') * Q := by simp only [mul_assoc]
    _ = (- (Q * Γ)) * Q' + (- (Q' * Γ)) * Q := by rw [h1, h2]
    _ = - ((Q * Γ) * Q') + - ((Q' * Γ) * Q) := by simp only [neg_mul]
    _ = - (Q * (Γ * Q')) - (Q' * (Γ * Q)) := by simp only [mul_assoc, sub_eq_add_neg]
    _ = - (Q * (- (Q' * Γ))) - (Q' * (- (Q * Γ))) := by rw [h1, h2]
    _ = - (- (Q * (Q' * Γ))) - (- (Q' * (Q * Γ))) := by simp only [mul_neg]
    _ = Q * (Q' * Γ) + Q' * (Q * Γ) := by simp only [neg_neg, sub_neg_eq_add]
    _ = (Q * Q') * Γ + (Q' * Q) * Γ := by simp only [mul_assoc]
    _ = (Q * Q' + Q' * Q) * Γ := (add_mul (Q * Q') (Q' * Q) Γ).symm

end NoncommutativeGeometry
