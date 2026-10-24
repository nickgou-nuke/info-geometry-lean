/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Singular.SquareZeroMoorePenrose

/-!
# Joint spectral/metric Peirce parity

All inverses are supplied native witnesses, never existence assumptions hidden
in the word "operator". The sign of `leftAnomaly` follows the intake: spectral
projector first. The existing `projectionDefect` uses the reverse sign; the
bridge below records that difference. The general MP support difference is
self-adjoint, but it is not asserted to be an involution or a tripotent.
-/

namespace InfoGeometry.Canonical.DrazinMPCartan

open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MetricAlgebraicProjectionDefect

variable {R : Type*} [Ring R]

/-- The first two stages only need reflexive inverse equations, not a star. -/
theorem reflexive_squareZero_supports {d b : R}
    (hinner : d * b * d = d) (houter : b * d * b = b) (hd : d * d = 0) :
    IsIdempotentElem (d * b) ∧ IsIdempotentElem (b * d) ∧
    (b * d) * (d * b) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change (d * b) * (d * b) = d * b
    calc
      _ = (d * b * d) * b := by simp only [mul_assoc]
      _ = _ := by rw [hinner]
  · change (b * d) * (b * d) = b * d
    calc
      _ = (b * d * b) * d := by simp only [mul_assoc]
      _ = _ := by rw [houter]
  · calc
      _ = b * (d * d) * b := by simp only [mul_assoc]
      _ = 0 := by rw [hd, mul_zero, zero_mul]

/-- Spectral-first sign convention for the left metric/spectral mismatch. -/
def leftAnomaly (a d m : R) : R := commutatorDefect (projection a d) (a * m)

/-- Spectral-first sign convention for the right metric/spectral mismatch. -/
def rightAnomaly (a d m : R) : R := commutatorDefect (projection a d) (m * a)

/-- The spectral projector, operator, inverse, and nilpotent summand are even. -/
theorem spectral_data_even {a d : R} {k : ℕ} (hD : IsDrazinInverse a d k) :
    evenPart (projection a d) a = a ∧ oddPart (projection a d) a = 0 ∧
    evenPart (projection a d) d = d ∧ oddPart (projection a d) d = 0 ∧
    evenPart (projection a d) (projection a d) = projection a d ∧
    oddPart (projection a d) (fittingNilpotentPart a d) = 0 := by
  have hp := projection_is_idempotent hD
  have ha := projection_comm_self hD
  have hd := projection_comm hD
  have hn : projection a d * fittingNilpotentPart a d =
      fittingNilpotentPart a d * projection a d := by
    change projection a d * (a * complementaryProjection a d) =
      (a * complementaryProjection a d) * projection a d
    calc
      _ = (projection a d * a) * complementaryProjection a d := by rw [mul_assoc]
      _ = (a * projection a d) * complementaryProjection a d := by rw [ha]
      _ = 0 := by rw [mul_assoc, projection_mul_complementaryProjection hD, mul_zero]
      _ = _ := by rw [mul_assoc, complementaryProjection_mul_projection hD, mul_zero]
  exact ⟨even_eq_self_of_commute hp ha, (odd_zero_iff_commute hp a).2 ha,
    even_eq_self_of_commute hp hd, (odd_zero_iff_commute hp d).2 hd,
    even_eq_self_of_commute hp rfl, (odd_zero_iff_commute hp _).2 hn⟩

/-- These parity formulas need only the Drazin witness; `m` may be arbitrary. -/
theorem anomaly_identities {a d : R} {k : ℕ} (hD : IsDrazinInverse a d k) (m : R) :
    oddPart (projection a d) (a * m) = reflection (projection a d) * leftAnomaly a d m ∧
    oddPart (projection a d) (m * a) = reflection (projection a d) * rightAnomaly a d m ∧
    oddPart (projection a d) (m * a - a * m) =
      reflection (projection a d) * (rightAnomaly a d m - leftAnomaly a d m) ∧
    reflection (projection a d) * leftAnomaly a d m +
      leftAnomaly a d m * reflection (projection a d) = 0 ∧
    reflection (projection a d) * rightAnomaly a d m +
      rightAnomaly a d m * reflection (projection a d) = 0 := by
  have hp := projection_is_idempotent hD
  refine ⟨odd_eq_reflection_commutator hp _, odd_eq_reflection_commutator hp _,
    ?_, (commutator_is_odd hp _).2, (commutator_is_odd hp _).2⟩
  rw [oddPart_sub, odd_eq_reflection_commutator hp, odd_eq_reflection_commutator hp]
  exact (mul_sub _ _ _).symm

/-- The doubled commutator formula is valid without inverting two. -/
theorem grading_commutator (a d m : R) :
    commutatorDefect (reflection (projection a d)) (m * a - a * m) =
      2 • (rightAnomaly a d m - leftAnomaly a d m) := by
  simp only [reflection, two_nsmul, leftAnomaly, rightAnomaly, commutatorDefect]
  noncomm_ring

/-- Both directed anomaly corners return to square-zero without metric assumptions. -/
theorem anomaly_corners_square_zero {a d : R} {k : ℕ}
    (hD : IsDrazinInverse a d k) (y : R) :
    component10 (projection a d) y * component10 (projection a d) y = 0 ∧
    component01 (projection a d) y * component01 (projection a d) y = 0 :=
  corners_square_zero (projection_is_idempotent hD) y

section Star
variable [StarRing R]

/-- Native MP supports and dual square-zero theorem close the lower ladder. -/
theorem squareZero_mp_to_reflection {d b : R}
    (hMP : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    IsStarProjection (d * b) ∧ IsStarProjection (b * d) ∧ b * b = 0 ∧
    reflection (d * b) * reflection (d * b) = 1 ∧
    star (reflection (d * b)) = reflection (d * b) ∧
    oddPart (d * b) d = d ∧ oddPart (d * b) b = b := by
  obtain ⟨hp, hq⟩ := InfoGeometry.Singular.ProjectionSectors.mp_supports hMP
  have hb := hMP.inverse_sq_eq_zero hd
  refine ⟨hp, hq, hb, reflection_sq hp.isIdempotentElem.eq,
    reflection_star hMP.ab_adj_eq, ?_, ?_⟩
  · have hpd : (d * b) * d = d := hMP.aba_eq_a
    have hdp : d * (d * b) = 0 := by rw [← mul_assoc, hd, zero_mul]
    simp only [oddPart, component10, component01, complementIdempotent,
      mul_sub, sub_mul, mul_one, one_mul, hpd, hdp, sub_self, sub_zero,
      zero_mul, add_zero]
  · have hpb : (d * b) * b = 0 := by rw [mul_assoc, hb, mul_zero]
    have hbp : b * (d * b) = b := by simpa only [mul_assoc] using hMP.bab_eq_b
    simp only [oddPart, component10, component01, complementIdempotent,
      mul_sub, sub_mul, mul_one, one_mul, hpb, hbp, sub_self, sub_zero,
      zero_mul, zero_add]

/-- The support difference is self-adjoint even when it is not a grading. -/
theorem mp_difference_star {a m : R} (hMP : IsMoorePenroseInverse a m) :
    star (m * a - a * m) = m * a - a * m := by
  rw [star_sub, hMP.ba_adj_eq, hMP.ab_adj_eq]

/-- Reconcile the opposite sign convention of the existing defect owner. -/
theorem leftAnomaly_eq_neg_projectionDefect {a d m : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse a m)
    (hD : InfoGeometry.Singular.Drazin.IsDrazinInverse a d k) :
    leftAnomaly a d m = -projectionDefect a m d k hMP hD := by
  change (a * d) * (a * m) - (a * m) * (a * d) =
    -((a * m) * (a * d) - (a * d) * (a * m))
  abel

/-- Conditional seven-stage synthesis using the actual repo-owned inverse predicates. -/
theorem drazin_mp_joint_cartan_synthesis {a d m : R} {k : ℕ}
    (hD : IsDrazinInverse a d k) (hMP : IsMoorePenroseInverse a m) :
    IsIdempotentElem (projection a d) ∧
    IsStarProjection (a * m) ∧ IsStarProjection (m * a) ∧
    reflection (projection a d) * reflection (projection a d) = 1 ∧
    fittingNilpotentPart a d ^ (k + 1) = 0 ∧
    oddPart (projection a d) a = 0 ∧
    oddPart (projection a d) (a * m) = reflection (projection a d) * leftAnomaly a d m ∧
    oddPart (projection a d) (m * a) = reflection (projection a d) * rightAnomaly a d m ∧
    reflection (projection a d) * leftAnomaly a d m +
      leftAnomaly a d m * reflection (projection a d) = 0 ∧
    reflection (projection a d) * rightAnomaly a d m +
      rightAnomaly a d m * reflection (projection a d) = 0 := by
  obtain ⟨hp, hq⟩ := InfoGeometry.Singular.ProjectionSectors.mp_supports hMP
  have hs := anomaly_identities hD m
  exact ⟨projection_is_idempotent hD, hp, hq,
    reflection_sq (projection_is_idempotent hD), fittingNilpotentPart_pow_succ_eq_zero hD,
    (spectral_data_even hD).2.1, hs.1, hs.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

/-- The return to MP structure is conditional on a supplied inverse of the corner. -/
theorem corner_to_new_reflection {p y b : R} (hp : p * p = p)
    (hb : IsMoorePenroseInverse (component10 p y) b) :
    IsStarProjection (component10 p y * b) ∧
    b * b = 0 ∧
    reflection (component10 p y * b) * reflection (component10 p y * b) = 1 := by
  have h := squareZero_mp_to_reflection hb (corners_square_zero hp y).1
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

end Star
end InfoGeometry.Canonical.DrazinMPCartan
