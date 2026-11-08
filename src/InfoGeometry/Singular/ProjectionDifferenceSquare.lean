/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.ProjectionDifferenceTripotence

/-!
# Idempotence of the squared difference of projections

Contract: on a C-star ring, the squared difference of two star projections
is idempotent precisely when they commute. The ring-level defect is owned by
`ProjectionSectors.boundary_idempotence_defect`; C-star definiteness is the
additional hypothesis needed here. Nilpotency of an underlying operator is
not a replacement for support commutation.
-/

namespace InfoGeometry.Singular.ProjectionSectors

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] {p q : A}

theorem boundary_square_idempotent_iff_commute (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    IsIdempotentElem ((p - q)^2) ↔ Commute p q := by
  constructor
  · intro h
    have hc : (p * q - q * p)^2 = 0 := by
      have hb := boundary_idempotence_defect hp.isIdempotentElem.eq hq.isIdempotentElem.eq
      rw [pow_two, h.eq, sub_self] at hb
      exact hb.symm
    have hs : star (p * q - q * p) = -(p * q - q * p) := by
      simp only [star_sub, star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
      abel
    have hz : star (p * q - q * p) * (p * q - q * p) = 0 := by
      rw [hs, neg_mul, ← pow_two, hc, neg_zero]
    exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)
  · intro h
    exact (boundary_square_projection hp hq h).isIdempotentElem

theorem boundary_square_projection_iff_commute (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    IsStarProjection ((p - q)^2) ↔ Commute p q := by
  constructor
  · intro h
    exact (boundary_square_idempotent_iff_commute hp hq).1 h.isIdempotentElem
  · exact boundary_square_projection hp hq

theorem mp_support_boundary_idempotent_iff {a m : A}
    (h : MoorePenrose.IsMoorePenroseInverse a m) :
    IsIdempotentElem ((a * m - m * a)^2) ↔ Commute (a * m) (m * a) := by
  obtain ⟨hp, hq⟩ := mp_supports h
  exact boundary_square_idempotent_iff_commute hp hq

end InfoGeometry.Singular.ProjectionSectors
