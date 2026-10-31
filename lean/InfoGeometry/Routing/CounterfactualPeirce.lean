/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FactLogicBypassAlgebra
import Mathlib.Tactic.NoncommRing

/-!
# Complementary-corner interventions in a noncommutative ring

An intervention at an idempotent `P` retains the complementary corner of an
operator. Its contrast is the part removed by that compression. The results
are purely algebraic and make no model-specific claim about causal inference.
-/

namespace InfoGeometry.Routing.CounterfactualPeirce

variable {B : Type*} [Ring B]

/-- Compression to the corner complementary to `P`. -/
def cornerIntervention (P T : B) : B := (1 - P) * T * (1 - P)

/-- Difference between an operator and its complementary-corner compression. -/
def cornerContrast (P T : B) : B := T - cornerIntervention P T

/-- The contrast consists of the two incident off-diagonal corners and the
intervened diagonal corner. -/
theorem cornerContrast_expand (P T : B) :
    cornerContrast P T = P * T + T * P - P * T * P := by
  simp only [cornerContrast, cornerIntervention]
  noncomm_ring

/-- Left multiplication by the intervention idempotent recovers the complete
left incident part of the operator. -/
theorem cornerContrast_left (P T : B) (hP : P * P = P) :
    P * cornerContrast P T = P * T := by
  have hpq : P * (1 - P) = 0 := by noncomm_ring [hP]
  simp only [cornerContrast, cornerIntervention]
  calc
    P * (T - (1 - P) * T * (1 - P)) =
        P * T - (P * (1 - P)) * T * (1 - P) := by noncomm_ring
    _ = P * T := by rw [hpq]; simp

/-- Right multiplication by the intervention idempotent recovers the complete
right incident part of the operator. -/
theorem cornerContrast_right (P T : B) (hP : P * P = P) :
    cornerContrast P T * P = T * P := by
  have hqp : (1 - P) * P = 0 := by noncomm_ring [hP]
  simp only [cornerContrast, cornerIntervention]
  calc
    (T - (1 - P) * T * (1 - P)) * P =
        T * P - (1 - P) * T * ((1 - P) * P) := by noncomm_ring
    _ = T * P := by rw [hqp]; simp

/-- The complementary compression removes the contrast completely. -/
theorem complementary_corner_contrast_zero (P T : B) (hP : P * P = P) :
    (1 - P) * cornerContrast P T * (1 - P) = 0 := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by noncomm_ring [hP]
  simp only [cornerContrast, cornerIntervention]
  calc
    (1 - P) * (T - (1 - P) * T * (1 - P)) * (1 - P) =
        (1 - P) * T * (1 - P) - ((1 - P) * (1 - P)) * T *
          ((1 - P) * (1 - P)) := by noncomm_ring
    _ = 0 := by rw [hQ]; simp

/-- An orthogonal corner has zero compression of the contrast. -/
theorem orthogonal_corner_contrast_zero (P R T : B)
    (hPR : P * R = 0) (hRP : R * P = 0) :
    R * cornerContrast P T * R = 0 := by
  have hRQ : R * (1 - P) = R := by
    calc
      R * (1 - P) = R - R * P := by noncomm_ring
      _ = R := by rw [hRP]; simp
  have hQR : (1 - P) * R = R := by
    calc
      (1 - P) * R = R - P * R := by noncomm_ring
      _ = R := by rw [hPR]; simp
  simp only [cornerContrast, cornerIntervention]
  calc
    R * (T - (1 - P) * T * (1 - P)) * R =
        R * T * R - (R * (1 - P)) * T * ((1 - P) * R) := by noncomm_ring
    _ = 0 := by rw [hRQ, hQR]; simp

/-- Two complementary-corner interventions commute when their idempotents
commute. -/
theorem cornerIntervention_commute (P Q T : B)
    (hPQ : P * Q = Q * P) :
    cornerIntervention P (cornerIntervention Q T) =
      cornerIntervention Q (cornerIntervention P T) := by
  have hcomp : (1 - P) * (1 - Q) = (1 - Q) * (1 - P) := by
    noncomm_ring [hPQ]
  calc
    cornerIntervention P (cornerIntervention Q T) =
        ((1 - P) * (1 - Q)) * T * ((1 - Q) * (1 - P)) := by
          simp [cornerIntervention, mul_assoc]
    _ = ((1 - Q) * (1 - P)) * T * ((1 - P) * (1 - Q)) := by rw [hcomp]
    _ = cornerIntervention Q (cornerIntervention P T) := by
          simp [cornerIntervention, mul_assoc]

/-- The operator splits into its retained complementary corner and contrast. -/
theorem cornerIntervention_add_contrast (P T : B) :
    cornerIntervention P T + cornerContrast P T = T := by
  simp [cornerContrast]

end InfoGeometry.Routing.CounterfactualPeirce
