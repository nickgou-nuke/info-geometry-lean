import Mathlib

/-!
# Chiral Parity Superalgebra

This file establishes the native non-commutative geometric structure of
the chiral superalgebra over an abstract ring.

We strictly prove that the anticommutator of two Odd chiral supercharges
yields an Even operator (the central supercharge condensation), without
relying on commutative toys or matrix simplifications.
-/

namespace InfoGeometry.ChiralParitySuperalgebra

variable {A : Type*} [Ring A]

def anticomm (X Y : A) : A := X * Y + Y * X

class IsChiralSupercharge (Gamma Q : A) : Prop where
  odd_comm : Gamma * Q = - (Q * Gamma)

def isEven (Gamma Z : A) : Prop :=
  Gamma * Z = Z * Gamma

/-- The fundamental theorem of the chiral superalgebra:
    The anticommutator of two Odd supercharges is Even. -/
theorem superalgebra_closure (Gamma Q Q' : A)
    [hQ : IsChiralSupercharge Gamma Q] [hQ' : IsChiralSupercharge Gamma Q'] :
    isEven Gamma (anticomm Q Q') := by
  dsimp [isEven, anticomm]
  rw [mul_add, add_mul]

  have h1 : Gamma * Q = - (Q * Gamma) := hQ.odd_comm
  have h2 : Gamma * Q' = - (Q' * Gamma) := hQ'.odd_comm

  -- Push Gamma through Q * Q'
  have step1 : Gamma * (Q * Q') = (Gamma * Q) * Q' := by rw [← mul_assoc]
  have step2 : (Gamma * Q) * Q' = - (Q * Gamma) * Q' := by rw [h1]
  have step3 : - (Q * Gamma) * Q' = - (Q * (Gamma * Q')) := by rw [neg_mul, ← mul_assoc]
  have step4 : - (Q * (Gamma * Q')) = - (Q * (- (Q' * Gamma))) := by rw [h2]
  have step5 : - (Q * (- (Q' * Gamma))) = Q * Q' * Gamma := by
    rw [mul_neg, neg_neg, mul_assoc]
  have term1 : Gamma * (Q * Q') = Q * Q' * Gamma := by
    rw [step1, step2, step3, step4, step5]

  -- Push Gamma through Q' * Q
  have step1_p : Gamma * (Q' * Q) = (Gamma * Q') * Q := by rw [← mul_assoc]
  have step2_p : (Gamma * Q') * Q = - (Q' * Gamma) * Q := by rw [h2]
  have step3_p : - (Q' * Gamma) * Q = - (Q' * (Gamma * Q)) := by rw [neg_mul, ← mul_assoc]
  have step4_p : - (Q' * (Gamma * Q)) = - (Q' * (- (Q * Gamma))) := by rw [h1]
  have step5_p : - (Q' * (- (Q * Gamma))) = Q' * Q * Gamma := by
    rw [mul_neg, neg_neg, mul_assoc]
  have term2 : Gamma * (Q' * Q) = Q' * Q * Gamma := by
    rw [step1_p, step2_p, step3_p, step4_p, step5_p]

  rw [term1, term2]

end InfoGeometry.ChiralParitySuperalgebra
