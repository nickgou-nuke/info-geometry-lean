/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Division-free tripotent defect identities

For an element `T` of an arbitrary (possibly noncommutative) ring, the
polynomial `T^3 - T` controls the failures of the three usual color expressions
to be orthogonal projectors. The identities here are polynomial identities;
they do not assert a Lie algebra or a group action. The color expressions are
scaled projectors in general, and become projector data only under additional
hypotheses (including tripotency and suitable handling of the factor `2`).
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The tripotent defect polynomial `T³ - T`. -/
def tripotentDefect (T : B) : B := T * T * T - T

/-- The zero-color polynomial `1 - T²`. -/
def triProj0 (T : B) : B := 1 - T * T

/-- The positive-color polynomial `T² + T`. -/
def triProjPlus (T : B) : B := T * T + T

/-- The negative-color polynomial `T² - T`. -/
def triProjMinus (T : B) : B := T * T - T

theorem tripotentDefect_eq_add_one_mul_defect (T : B) :
    tripotentDefect T = (T + 1) * (T * T - T) := by
  simp only [tripotentDefect]
  noncomm_ring

theorem tripotentDefect_eq_sub_one_mul_defectBar (T : B) :
    tripotentDefect T = (T - 1) * (T * T + T) := by
  simp only [tripotentDefect]
  noncomm_ring

theorem triProj_scaled_partition (T : B) :
    (2 : ℤ) • triProj0 T + triProjPlus T + triProjMinus T =
      (2 : ℤ) • (1 : B) := by
  simp only [triProj0, triProjPlus, triProjMinus, two_zsmul]
  noncomm_ring

theorem triProj_scaled_reconstruction (T : B) :
    triProjPlus T - triProjMinus T = (2 : ℤ) • T := by
  simp only [triProjPlus, triProjMinus, two_zsmul]
  noncomm_ring

theorem triProjPlus_mul_triProjMinus (T : B) :
    triProjPlus T * triProjMinus T = T * tripotentDefect T := by
  simp only [triProjPlus, triProjMinus, tripotentDefect]
  noncomm_ring

theorem triProj0_mul_triProjPlus (T : B) :
    triProj0 T * triProjPlus T = -tripotentDefect T * (T + 1) := by
  simp only [triProj0, triProjPlus, tripotentDefect]
  noncomm_ring

theorem triProj0_mul_triProjMinus (T : B) :
    triProj0 T * triProjMinus T = tripotentDefect T * (1 - T) := by
  simp only [triProj0, triProjMinus, tripotentDefect]
  noncomm_ring

theorem triProjMinus_square_residual (T : B) :
    triProjMinus T * triProjMinus T - (2 : ℤ) • triProjMinus T =
      (T - (2 : ℤ) • (1 : B)) * tripotentDefect T := by
  simp only [triProjMinus, tripotentDefect, two_zsmul]
  noncomm_ring

theorem triProjPlus_square_residual (T : B) :
    triProjPlus T * triProjPlus T - (2 : ℤ) • triProjPlus T =
      (T + (2 : ℤ) • (1 : B)) * tripotentDefect T := by
  simp only [triProjPlus, tripotentDefect, two_zsmul]
  noncomm_ring

/-- Under tripotency, the zero-color polynomial is an idempotent. -/
theorem triProj0_idempotent_of_tripotent {T : B}
    (hT : T * T * T = T) : triProj0 T * triProj0 T = triProj0 T := by
  have hT4 : T * T * T * T = T * T := by
    calc
      T * T * T * T = (T * T * T) * T := rfl
      _ = T * T := by rw [hT]
  have hSquare : (T * T) * (T * T) = T * T := by
    calc
      (T * T) * (T * T) = T * T * T * T := by noncomm_ring
      _ = T * T := hT4
  simp only [triProj0]
  calc
    (1 - T * T) * (1 - T * T) = 1 - (2 : ℤ) • (T * T) + (T * T) * (T * T) := by
      noncomm_ring
    _ = 1 - T * T := by rw [hSquare]; noncomm_ring

/--
Under tripotency, the positive and negative color polynomials are orthogonal
and are twice idempotent. The factor `2` is retained explicitly; no division
or characteristic restriction is hidden here.
-/
theorem tripotent_scaled_color_projector_laws {T : B}
    (hT : T * T * T = T) :
    triProjPlus T * triProjMinus T = 0 ∧
    triProj0 T * triProjPlus T = 0 ∧
    triProj0 T * triProjMinus T = 0 ∧
    triProjPlus T * triProjPlus T = (2 : ℤ) • triProjPlus T ∧
    triProjMinus T * triProjMinus T = (2 : ℤ) • triProjMinus T := by
  have hdef : tripotentDefect T = 0 := by
    simp only [tripotentDefect, hT, sub_self]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [triProjPlus_mul_triProjMinus, hdef, mul_zero]
  · rw [triProj0_mul_triProjPlus, hdef, neg_zero, zero_mul]
  · rw [triProj0_mul_triProjMinus, hdef, zero_mul]
  · have h := triProjPlus_square_residual T
    simp only [hdef, mul_zero, sub_eq_zero] at h
    exact h
  · have h := triProjMinus_square_residual T
    simp only [hdef, mul_zero, sub_eq_zero] at h
    exact h

/-- Difference of two orthogonal idempotents. -/
def colorTripotent (P_R P_G : B) : B := P_R - P_G

/-- Complementary third corner for two orthogonal idempotents. -/
def colorBlue (P_R P_G : B) : B := 1 - P_R - P_G

/--
Two orthogonal idempotents produce a tripotent, a complementary idempotent,
and the characteristic-free scaled color readouts. This is an associative
ring statement, with no matrix diagonalization or commutativity assumption.
-/
theorem orthogonal_idempotents_color_tripotent
    {P_R P_G : B}
    (hR : P_R * P_R = P_R) (hG : P_G * P_G = P_G)
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) :
    tripotentDefect (colorTripotent P_R P_G) = 0 ∧
    colorBlue P_R P_G * colorBlue P_R P_G = colorBlue P_R P_G ∧
    triProjPlus (colorTripotent P_R P_G) = (2 : ℤ) • P_R ∧
    triProjMinus (colorTripotent P_R P_G) = (2 : ℤ) • P_G ∧
    triProj0 (colorTripotent P_R P_G) = colorBlue P_R P_G := by
  simp only [tripotentDefect, colorTripotent, colorBlue, triProjPlus,
    triProjMinus, triProj0, two_zsmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    noncomm_ring [hR, hG, hRG, hGR]

/-- The commutator with the difference of two orthogonal idempotents has
charges `2`, `-2`, `1`, `1`, `-1`, `-1`, and `0` on the corresponding
red/green/blue Peirce blocks. This is an associative-ring corner identity;
it does not assert an identification with a Lie algebra representation. -/
theorem colorTripotent_corner_charge
    {P_R P_G : B}
    (hR : P_R * P_R = P_R) (hG : P_G * P_G = P_G)
    (hRG : P_R * P_G = 0) (hGR : P_G * P_R = 0) (X : B) :
    comm (colorTripotent P_R P_G) (P_R * X * P_G) =
      (2 : ℤ) • (P_R * X * P_G) ∧
    comm (colorTripotent P_R P_G) (P_G * X * P_R) =
      -((2 : ℤ) • (P_G * X * P_R)) ∧
    comm (colorTripotent P_R P_G) (P_R * X * colorBlue P_R P_G) =
      P_R * X * colorBlue P_R P_G ∧
    comm (colorTripotent P_R P_G) (colorBlue P_R P_G * X * P_G) =
      colorBlue P_R P_G * X * P_G ∧
    comm (colorTripotent P_R P_G) (colorBlue P_R P_G * X * P_R) =
      -(colorBlue P_R P_G * X * P_R) ∧
    comm (colorTripotent P_R P_G) (P_G * X * colorBlue P_R P_G) =
      -(P_G * X * colorBlue P_R P_G) ∧
    comm (colorTripotent P_R P_G)
      (P_R * X * P_R + P_G * X * P_G +
        colorBlue P_R P_G * X * colorBlue P_R P_G) = 0 := by
  simp only [colorTripotent, colorBlue, comm, two_zsmul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    noncomm_ring [hR, hG, hRG, hGR] <;>
    simp only [← mul_assoc, hR, hG, hRG, hGR, zero_mul, zero_add, add_zero] <;> abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
