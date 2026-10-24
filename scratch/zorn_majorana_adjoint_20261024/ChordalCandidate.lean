/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceRotorAction

/-! Algebraic compression and displacement identities for the existing rotor
orbit. Scalars are central; no metric, positivity or analytic angle is used. -/
namespace InfoGeometry.Canonical.PeirceRotorChordal
open ReflexiveNilpotentFlows PeirceRotorAction
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d B : A} (hd : d*d=0) (hB : B*B=0)
  (hr : d*B*d=d) (hs : B*d*B=B)

theorem plus_mul_movingPlus (c s : R) :
    (d*B)*movingPlus c s d B = (c*c) • (d*B) - (c*s) • d := by
  obtain ⟨hpp, _, hpq, _, _, _, _, _, _⟩ := support_table hd hB hr hs
  have hpB : (d*B)*B=0 := by rw [mul_assoc, hB, mul_zero]
  rw [movingPlus_expansion hd hB hr hs]
  simp only [mul_sub, mul_add, mul_smul_comm, hpp, hpq, hr, hpB,
    smul_zero, add_zero]

theorem movingPlus_mul_plus (c s : R) :
    movingPlus c s d B*(d*B) = (c*c) • (d*B) - (c*s) • B := by
  obtain ⟨hpp, _, _, hqp, _, _, _, _, _⟩ := support_table hd hB hr hs
  have hdp : d*(d*B)=0 := by rw [← mul_assoc, hd, zero_mul]
  have hBp : B*(d*B)=B := by rw [← mul_assoc, hs]
  rw [movingPlus_expansion hd hB hr hs]
  simp only [sub_mul, add_mul, smul_mul_assoc, hpp, hqp, hdp, hBp,
    smul_zero, add_zero, zero_add]

theorem plus_movingPlus_sandwich (c s : R) :
    (d*B)*movingPlus c s d B*(d*B) = (c*c) • (d*B) := by
  rw [plus_mul_movingPlus hd hB hr hs]
  have hpp := (support_table hd hB hr hs).1
  have hdp : d*(d*B)=0 := by rw [← mul_assoc, hd, zero_mul]
  simp only [sub_mul, smul_mul_assoc, hpp, hdp, smul_zero, sub_zero]

theorem movingPlus_displacement_square (c s : R) (hc : c*c+s*s=1) :
    (movingPlus c s d B-d*B)*(movingPlus c s d B-d*B) =
      (s*s) • support d B := by
  have hMM := (movingPlus_idempotent hd hB hr hs c s hc).eq
  have hpp := (support_table hd hB hr hs).1
  calc
    _ = movingPlus c s d B* movingPlus c s d B -
        movingPlus c s d B*(d*B) - (d*B)*movingPlus c s d B +
        (d*B)*(d*B) := by noncomm_ring
    _ = (s*s) • support d B := by
      rw [hMM, hpp, movingPlus_mul_plus hd hB hr hs,
        plus_mul_movingPlus hd hB hr hs, movingPlus_expansion hd hB hr hs]
      have hcc : c*c=1-s*s := eq_sub_of_add_eq hc
      rw [hcc]
      simp only [support, sub_smul, one_smul, smul_add]
      abel

end InfoGeometry.Canonical.PeirceRotorChordal
