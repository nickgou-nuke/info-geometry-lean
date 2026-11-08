/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceRotorChordal
import InfoGeometry.Canonical.PeirceWeightedTrace

/-! The diagonal part of the existing rotor orbit is an existing support weight.
No positivity, normalization, or analytic KMS property is inferred. -/
namespace InfoGeometry.Canonical.PeirceRotorDiagonalWeight
open ReflexiveNilpotentFlows PeirceRotorAction PeirceRotorChordal PeirceWeightedTrace
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d B : A} (hd : d*d=0) (hB : B*B=0)
  (hr : d*B*d=d) (hs : B*d*B=B)
include hd hB hr hs

theorem minus_movingPlus_sandwich (c s : R) :
    (B*d)*movingPlus c s d B*(B*d) = (s*s) • (B*d) := by
  obtain ⟨_, hqq, _, hqp, _⟩ := support_table hd hB hr hs
  have hqd : (B*d)*d=0 := by rw [mul_assoc, hd, mul_zero]
  have hBq : B*(B*d)=0 := by rw [← mul_assoc, hB, zero_mul]
  rw [movingPlus_expansion hd hB hr hs]
  simp only [mul_sub, mul_add, sub_mul, mul_smul_comm,
    smul_mul_assoc, hqp, hqq, hqd, hs, hBq,
    zero_add, smul_zero, sub_zero]

theorem rotor_diagonal_eq_weight (c s : R) :
    (d*B)*movingPlus c s d B*(d*B) + (B*d)*movingPlus c s d B*(B*d) =
      supportWeight (s*s) (c*c) d B := by
  rw [plus_movingPlus_sandwich hd hB hr hs, minus_movingPlus_sandwich hd hB hr hs]
  exact add_comm _ _

theorem rotor_off_diagonal (c s : R) :
    movingPlus c s d B - supportWeight (s*s) (c*c) d B = -(c*s) • (d+B) := by
  rw [movingPlus_expansion hd hB hr hs]
  simp only [supportWeight, neg_smul]
  abel

end InfoGeometry.Canonical.PeirceRotorDiagonalWeight
