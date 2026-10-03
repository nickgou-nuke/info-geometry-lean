import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

namespace InfoGeometry.GrandUnification.SplitArchetypeDictionary

variable {R A : Type*} [CommRing R] [Invertible (2 : R)] [Ring A] [Algebra R A]

/-- A split involution is an element $\epsilon$ whose square is the identity,
representing the chiral volume element in split signature (e.g., $C\ell(1,1)$). -/
structure SplitInvolution (R A : Type*) [CommRing R] [Invertible (2 : R)] [Ring A] [Algebra R A] where
  epsilon : A
  sq_eq_one : epsilon * epsilon = 1

namespace SplitInvolution

variable (inv : SplitInvolution R A)

/-- The positive chiral split Peirce projector P_+ = (1 + ε)/2. -/
def P_plus : A :=
  (⅟(2 : R)) • (1 + inv.epsilon)

/-- The negative chiral split Peirce projector P_- = (1 - ε)/2. -/
def P_minus : A :=
  (⅟(2 : R)) • (1 - inv.epsilon)

theorem P_plus_add_P_minus : inv.P_plus + inv.P_minus = 1 := by
  dsimp [P_plus, P_minus]
  rw [← smul_add]
  have h_sum : (1 : A) + inv.epsilon + ((1 : A) - inv.epsilon) = (2 : R) • (1 : A) := by
    calc
      (1 : A) + inv.epsilon + ((1 : A) - inv.epsilon) = (1 : A) + 1 := by noncomm_ring
      _ = (2 : R) • (1 : A) := by rw [two_smul]
  rw [h_sum, ← mul_smul, invOf_mul_self, one_smul]

theorem P_plus_sq : inv.P_plus * inv.P_plus = inv.P_plus := by
  dsimp [P_plus]
  rw [smul_mul_smul]
  have h_sq : (1 + inv.epsilon) * (1 + inv.epsilon) = (2 : R) • (1 + inv.epsilon) := by
    calc
      (1 + inv.epsilon) * (1 + inv.epsilon) = 1 + inv.epsilon + inv.epsilon + inv.epsilon * inv.epsilon := by noncomm_ring
      _ = 1 + inv.epsilon + inv.epsilon + 1 := by rw [inv.sq_eq_one]
      _ = (1 + inv.epsilon) + (1 + inv.epsilon) := by abel
      _ = (2 : R) • (1 + inv.epsilon) := by rw [two_smul]
  rw [h_sq, ← mul_smul]
  have h_coeff : (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) := by
    calc
      (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) * (⅟(2 : R) * 2) := by rw [mul_assoc]
      _ = ⅟(2 : R) * 1 := by rw [invOf_mul_self]
      _ = ⅟(2 : R) := by rw [mul_one]
  rw [h_coeff]

theorem P_minus_sq : inv.P_minus * inv.P_minus = inv.P_minus := by
  dsimp [P_minus]
  rw [smul_mul_smul]
  have h_sq : (1 - inv.epsilon) * (1 - inv.epsilon) = (2 : R) • (1 - inv.epsilon) := by
    calc
      (1 - inv.epsilon) * (1 - inv.epsilon) = 1 - inv.epsilon - inv.epsilon + inv.epsilon * inv.epsilon := by noncomm_ring
      _ = 1 - inv.epsilon - inv.epsilon + 1 := by rw [inv.sq_eq_one]
      _ = (1 - inv.epsilon) + (1 - inv.epsilon) := by abel
      _ = (2 : R) • (1 - inv.epsilon) := by rw [two_smul]
  rw [h_sq, ← mul_smul]
  have h_coeff : (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) := by
    calc
      (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) * (⅟(2 : R) * 2) := by rw [mul_assoc]
      _ = ⅟(2 : R) * 1 := by rw [invOf_mul_self]
      _ = ⅟(2 : R) := by rw [mul_one]
  rw [h_coeff]

theorem P_plus_mul_P_minus : inv.P_plus * inv.P_minus = 0 := by
  dsimp [P_plus, P_minus]
  rw [smul_mul_smul]
  have h_cross : (1 + inv.epsilon) * (1 - inv.epsilon) = 0 := by
    calc
      (1 + inv.epsilon) * (1 - inv.epsilon) = 1 - inv.epsilon * inv.epsilon := by noncomm_ring
      _ = 1 - 1 := by rw [inv.sq_eq_one]
      _ = 0 := by noncomm_ring
  rw [h_cross, smul_zero]

theorem P_minus_mul_P_plus : inv.P_minus * inv.P_plus = 0 := by
  dsimp [P_plus, P_minus]
  rw [smul_mul_smul]
  have h_cross : (1 - inv.epsilon) * (1 + inv.epsilon) = 0 := by
    calc
      (1 - inv.epsilon) * (1 + inv.epsilon) = 1 - inv.epsilon * inv.epsilon := by noncomm_ring
      _ = 1 - 1 := by rw [inv.sq_eq_one]
      _ = 0 := by noncomm_ring
  rw [h_cross, smul_zero]

end SplitInvolution
end InfoGeometry.GrandUnification.SplitArchetypeDictionary
