/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveNilpotentFlows

/-!
# Projector motion for the native reflexive rotor

Polynomial identities for a square-zero reflexive pair in an associative ring.
Scalar parameters are central through Algebra. Normalization is required only
for inverse-based idempotence and the fixed-support sum. No analytic flow,
star projection, or syntax/classification assertion is made.
-/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

open GrassmannianBundleCyclotomicOrientability

variable {A : Type*} [Ring A] {d B : A}

/-- The sign is negative for the convention J = d - B. -/
theorem skew_commutator_plus (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    lieBracket (d-B) (d*B) = -(d+B) := by
  calc
    _ = (d*d)*B - B*d*B - d*B*d + d*(B*B) := by
      unfold lieBracket; noncomm_ring
    _ = _ := by rw [hd, hB, hr, hs]; simp only [zero_mul, mul_zero, zero_sub, sub_zero]; abel

theorem skew_commutator_minus (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    lieBracket (d-B) (B*d) = d+B := by
  calc
    _ = d*B*d - (B*B)*d - B*(d*d) + B*d*B := by
      unfold lieBracket; noncomm_ring
    _ = _ := by rw [hd, hB, hr, hs]; simp

theorem skew_commutator_parity (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    lieBracket (d-B) (d*B-B*d) = -(2:A)*(d+B) := by
  calc
    _ = lieBracket (d-B) (d*B) - lieBracket (d-B) (B*d) := by
      unfold lieBracket; noncomm_ring
    _ = _ := by rw [skew_commutator_plus hd hB hr hs,
      skew_commutator_minus hd hB hr hs]; noncomm_ring

/-- This identity does not require the pair relations. -/
theorem skew_commutator_sum : lieBracket (d-B) (d+B) = (2:A)*(d*B-B*d) := by
  unfold lieBracket; noncomm_ring

theorem skew_double_commutator_parity (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    lieBracket (d-B) (lieBracket (d-B) (d*B-B*d)) = -(4:A)*(d*B-B*d) := by
  rw [skew_commutator_parity hd hB hr hs]
  calc
    _ = -(2:A)*lieBracket (d-B) (d+B) := by unfold lieBracket; noncomm_ring
    _ = _ := by rw [skew_commutator_sum]; noncomm_ring

/-- No cancellation of 2 or 4 is used, including in characteristic two. -/
theorem skew_commutator_plus_eq_zero_iff (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    lieBracket (d-B) (d*B) = 0 ↔ d=0 ∧ B=0 := by
  rw [skew_commutator_plus hd hB hr hs, neg_eq_zero]
  constructor
  · intro hq
    have hd0 : d=0 := by
      calc
        d = d*(d+B)*d := by rw [mul_add, add_mul, hd, zero_mul, zero_add, hr]
        _ = 0 := by rw [hq]; simp
    exact ⟨hd0, by simpa only [hd0, zero_add] using hq⟩
  · rintro ⟨rfl, rfl⟩; simp

section Scalars
variable {R : Type*} [CommRing R] [Algebra R A]
variable (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) (hs : B*d*B=B)

/-- Left multiplication of the plus idempotent by the actual native rotor. -/
theorem rotor_mul_plus (c s : R) :
    rotor c s d B * (d*B) = c • (d*B) - s • B := by
  obtain ⟨hpp, _, _, hmp, _, _, hcp, _, _⟩ := support_table hd hB hr hs
  have hsp : support d B * (d*B) = d*B := by
    simp only [support, add_mul, hpp, hmp, add_zero]
  have hjp : (d-B)*(d*B) = -B := by
    calc
      _ = (d*d)*B - B*d*B := by noncomm_ring
      _ = _ := by rw [hd, hs]; simp
  simp only [rotor, add_mul, smul_mul_assoc, hcp, hsp, hjp,
    zero_add, smul_neg, sub_eq_add_neg]

/-- Right multiplication keeps the parameter s independent and universally quantified. -/
theorem plus_mul_rotor (c s : R) :
    (d*B) * rotor c s d B = c • (d*B) + s • d := by
  obtain ⟨hpp, _, hpm, _, hpc, _, _, _, _⟩ := support_table hd hB hr hs
  have hps : (d*B)*support d B = d*B := by
    simp only [support, mul_add, hpp, hpm, add_zero]
  have hpj : (d*B)*(d-B) = d := by
    calc
      _ = d*B*d - d*(B*B) := by noncomm_ring
      _ = _ := by rw [hr, hB]; simp
  simp only [rotor, mul_add, mul_smul_comm, hpc, hps, hpj, zero_add]

theorem creator_mul_rotor (c s : R) :
    B * rotor c s d B = c • B + s • (B*d) := by
  have hbc := (complement_annihilates hd hB hr hs).2.2.2
  have hbs := (active_support_absorbs hd hB hr hs).2.2.2
  change B * support d B = B at hbs
  have hbj : B*(d-B) = B*d := by rw [mul_sub, hB, sub_zero]
  simp only [rotor, mul_add, mul_smul_comm, hbc, hbs, hbj, zero_add]

/-- Polynomial projector formula; no circle normalization is needed. -/
theorem rotor_conjugate_plus (c s : R) :
    rotor c s d B * (d*B) * rotor c (-s) d B =
      (c*c) • (d*B) + (s*s) • (B*d) - (c*s) • (d+B) := by
  rw [rotor_mul_plus hd hB hr hs]
  simp only [sub_mul, smul_mul_assoc, plus_mul_rotor hd hB hr hs,
    creator_mul_rotor hd hB hr hs, smul_add, smul_smul, mul_neg,
    neg_smul, smul_neg, mul_comm s c]
  abel

/-- Exchanging the two generators reverses the scalar skew parameter. -/
theorem rotor_swap_parameters (c s : R) : rotor c s B d = rotor c (-s) d B := by
  simp only [rotor, complement, support, add_comm (B*d) (d*B), neg_smul]
  rw [show B-d = -(d-B) by abel, smul_neg]

/-- The minus projector has the opposite mixed-term sign. -/
theorem rotor_conjugate_minus (c s : R) :
    rotor c s d B * (B*d) * rotor c (-s) d B =
      (c*c) • (B*d) + (s*s) • (d*B) + (c*s) • (d+B) := by
  have h := rotor_conjugate_plus hB hd hs hr c (-s)
  simpa only [rotor_swap_parameters, neg_neg, neg_mul_neg, mul_neg,
    neg_smul, sub_neg_eq_add, add_comm B d] using h

/-- Reverse inverse order, obtained from the native inverse theorem. -/
theorem rotor_reverse_inverse (c s : R) (hc : c*c+s*s=1) :
    rotor c (-s) d B * rotor c s d B = 1 := by
  simpa only [neg_mul_neg, neg_neg] using
    rotor_inverse hd hB hr hs c (-s) (by simpa only [neg_mul_neg] using hc)

theorem rotor_plus_idempotent (c s : R) (hc : c*c+s*s=1) :
    IsIdempotentElem (rotor c s d B * (d*B) * rotor c (-s) d B) := by
  exact isIdempotentElem_homogeneousProj
    (show IsIdempotentElem (d*B) from (support_table hd hB hr hs).1)
    (rotor_reverse_inverse hd hB hr hs c s hc)

theorem rotor_minus_idempotent (c s : R) (hc : c*c+s*s=1) :
    IsIdempotentElem (rotor c s d B * (B*d) * rotor c (-s) d B) := by
  exact isIdempotentElem_homogeneousProj
    (show IsIdempotentElem (B*d) from (support_table hd hB hr hs).2.1)
    (rotor_reverse_inverse hd hB hr hs c s hc)

theorem rotor_plus_mul_minus (c s : R) (hc : c*c+s*s=1) :
    (rotor c s d B * (d*B) * rotor c (-s) d B) *
      (rotor c s d B * (B*d) * rotor c (-s) d B) = 0 := by
  calc
    _ = rotor c s d B * (d*B) *
        (rotor c (-s) d B * rotor c s d B) * (B*d) * rotor c (-s) d B := by
          simp only [mul_assoc]
    _ = rotor c s d B * ((d*B)*(B*d)) * rotor c (-s) d B := by
      rw [rotor_reverse_inverse hd hB hr hs c s hc, mul_one]; simp only [mul_assoc]
    _ = 0 := by rw [(support_table hd hB hr hs).2.2.1]; simp

theorem rotor_minus_mul_plus (c s : R) (hc : c*c+s*s=1) :
    (rotor c s d B * (B*d) * rotor c (-s) d B) *
      (rotor c s d B * (d*B) * rotor c (-s) d B) = 0 := by
  have h := rotor_plus_mul_minus hB hd hs hr c (-s)
    (by simpa only [neg_mul_neg] using hc)
  simpa only [rotor_swap_parameters, neg_neg] using h

theorem rotor_projector_sum (c s : R) (hc : c*c+s*s=1) :
    rotor c s d B * (d*B) * rotor c (-s) d B +
      rotor c s d B * (B*d) * rotor c (-s) d B = support d B := by
  rw [rotor_conjugate_plus hd hB hr hs, rotor_conjugate_minus hd hB hr hs]
  calc
    _ = (c*c+s*s) • (d*B+B*d) := by simp only [add_smul, smul_add]; abel
    _ = support d B := by rw [hc, one_smul]; rfl

theorem rotor_projector_resolution (c s : R) (hc : c*c+s*s=1) :
    rotor c s d B * (d*B) * rotor c (-s) d B +
      rotor c s d B * (B*d) * rotor c (-s) d B + complement d B = 1 := by
  rw [rotor_projector_sum hd hB hr hs c s hc]
  unfold complement; abel

/-- A quarter-turn swaps the supports, in every characteristic. -/
theorem rotor_quarter_turn_plus :
    rotor (0:R) 1 d B * (d*B) * rotor (0:R) (-1) d B = B*d := by
  simpa only [zero_mul, one_mul, zero_smul, one_smul, zero_add, sub_zero] using
    rotor_conjugate_plus hd hB hr hs (0:R) 1

theorem rotor_quarter_turn_minus :
    rotor (0:R) 1 d B * (B*d) * rotor (0:R) (-1) d B = d*B := by
  simpa only [zero_mul, one_mul, zero_smul, one_smul, zero_add, add_zero] using
    rotor_conjugate_minus hd hB hr hs (0:R) 1

theorem rotor_quarter_turn_fixed_iff :
    rotor (0:R) 1 d B * (d*B) * rotor (0:R) (-1) d B = d*B ↔ d=0 ∧ B=0 := by
  rw [rotor_quarter_turn_plus hd hB hr hs]
  constructor
  · intro hp
    have hpp := (support_table hd hB hr hs).1
    have hpm := (support_table hd hB hr hs).2.2.1
    rw [hp] at hpm
    have hp0 : d*B=0 := hpp.symm.trans hpm
    have hm0 : B*d=0 := hp.trans hp0
    exact ⟨by simpa only [hp0, zero_mul] using hr.symm,
      by simpa only [hm0, zero_mul] using hs.symm⟩
  · rintro ⟨rfl, rfl⟩; simp

/-- Universal normalized motion is stationary exactly for the zero pair. -/
theorem rotor_no_turn_iff :
    (∀ c s : R, c*c+s*s=1 →
      rotor c s d B * (d*B) * rotor c (-s) d B = d*B) ↔ d=0 ∧ B=0 := by
  constructor
  · intro h
    exact (rotor_quarter_turn_fixed_iff (R:=R) hd hB hr hs).mp
      (h 0 1 (by simp))
  · rintro ⟨rfl, rfl⟩ c s _
    simp

end Scalars
end InfoGeometry.Canonical.ReflexiveNilpotentFlows
