/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenroseSectors
import Mathlib.Analysis.CStarAlgebra.Basic

/-! # Exact tripotence criteria for differences of projections

In a ring the criterion is equality of the two compressions. For star
projections in a C-star ring it is equivalent to commutation. Orthogonality
is sufficient but unnecessary. The existing oblique Moore–Penrose example
therefore does not justify an unconditional support-difference tripotence law.
-/

namespace InfoGeometry.Singular.ProjectionSectors

section Ring
variable {A : Type*} [Ring A] {p q : A}

/-- The complete cubic defect, without a commutation assumption. -/
theorem difference_cube_defect (hp : p * p = p) (hq : q * q = q) :
    (p - q)^3 - (p - q) = q * p * q - p * q * p := by
  noncomm_ring [hp, hq]

/-- Equality of compressions is the exact arbitrary-ring criterion. -/
theorem difference_tripotent_iff_compressions (hp : p * p = p) (hq : q * q = q) :
    (p - q)^3 = p - q ↔ p * q * p = q * p * q := by
  rw [← sub_eq_zero, difference_cube_defect hp hq, sub_eq_zero, eq_comm]

/-- Commuting idempotents need not be orthogonal for their difference to be tripotent. -/
theorem difference_tripotent_of_commute (hp : p * p = p) (hq : q * q = q)
    (h : Commute p q) : (p - q)^3 = p - q := by
  apply (difference_tripotent_iff_compressions hp hq).2
  calc p * q * p = q * p := by rw [h.eq, mul_assoc, hp]
    _ = q * p * q := by rw [mul_assoc, h.eq, ← mul_assoc, hq]

end Ring

section CStar
variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] {p q : A}

/-- C-star definiteness upgrades the compression criterion to commutation. -/
theorem difference_tripotent_iff_commute (hp : IsStarProjection p)
    (hq : IsStarProjection q) : (p - q)^3 = p - q ↔ Commute p q := by
  constructor
  · intro h3
    have h4 : (p - q)^4 = (p - q)^2 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, pow_two]
    have hc : (p * q - q * p)^2 = 0 := by
      have hb := boundary_idempotence_defect hp.isIdempotentElem.eq hq.isIdempotentElem.eq
      rw [← pow_mul] at hb
      norm_num only [Nat.reduceMul] at hb
      rw [h4, sub_self] at hb
      exact hb.symm
    have hs : star (p * q - q * p) = -(p * q - q * p) := by
      simp only [star_sub, star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
      abel
    have hz : star (p * q - q * p) * (p * q - q * p) = 0 := by
      rw [hs, neg_mul, ← pow_two, hc, neg_zero]
    exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)
  · exact difference_tripotent_of_commute hp.isIdempotentElem.eq hq.isIdempotentElem.eq

/-- Applied to the actual Moore–Penrose range and domain supports. -/
theorem mp_support_difference_tripotent_iff {a m : A}
    (h : MoorePenrose.IsMoorePenroseInverse a m) :
    (a * m - m * a)^3 = a * m - m * a ↔ Commute (a * m) (m * a) := by
  obtain ⟨hp, hq⟩ := mp_supports h
  exact difference_tripotent_iff_commute hp hq

end CStar
end InfoGeometry.Singular.ProjectionSectors
