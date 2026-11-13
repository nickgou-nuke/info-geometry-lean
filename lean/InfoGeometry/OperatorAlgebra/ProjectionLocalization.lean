/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionCStar
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Projection localization, leakage, and commutator variance

The carrier is an arbitrary associative star ring. Complementary localization
is a Gram conservation identity for a one-sided isometry. It does not assert
that conjugating a projection by that isometry gives another projection.

Projection compression uses the existing polarized Peirce defect theorem.
Order positivity and faithful vanishing are separated into their native
star-ordered and C-star hypotheses. No metric porosity or uncertainty exponent
is inferred from the algebraic identities.
-/

namespace InfoGeometry.OperatorAlgebra.ProjectionLocalization

open InfoGeometry.Core.PeirceCompressionDefect

section StarRing

variable {A : Type*} [Ring A] [StarRing A]

/-- An isometry sends the initial projection into complementary localization
channels whose two Gram operators sum to that initial projection. -/
theorem complementary_localization_gram {p q v : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv : star v * v = 1) :
    star (twoBoundaryCompression q v p) * twoBoundaryCompression q v p +
      star (twoBoundaryCompression (1 - q) v p) *
        twoBoundaryCompression (1 - q) v p = p := by
  have hsum : q * q + (1 - q) * (1 - q) = 1 := by
    rw [hq.isIdempotentElem.eq, hq.one_sub.isIdempotentElem.eq]
    simp
  unfold twoBoundaryCompression
  simp only [star_mul, star_sub, star_one,
    hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
  calc
    _ = p * star v * (q * q + (1 - q) * (1 - q)) * v * p := by
      noncomm_ring
    _ = p * (star v * v) * p := by rw [hsum]; simp only [mul_one, mul_assoc]
    _ = p := by rw [hv, mul_one, hp.isIdempotentElem.eq]

/-- Compressing a star projection gives a star-square idempotency defect.
This is a specialization of the existing polarized compression identity. -/
theorem compression_variance_eq_leakage {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p * q * p - (p * q * p) * (p * q * p) =
      star ((1 - p) * q * p) * ((1 - p) * q * p) := by
  simpa only [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq] using
    compression_adjoint_mul_defect p q q
      hp.isIdempotentElem.eq hp.isSelfAdjoint.star_eq

omit [StarRing A] in
/-- The commutator restricted to the initial corner is minus the leakage
operator. No properness of the involution is needed for this equality. -/
theorem commutator_mul_projection {p q : A} (hp : IsIdempotentElem p) :
    ⁅p, q⁆ * p = -((1 - p) * q * p) := by
  rw [Ring.lie_def]
  noncomm_ring [hp.eq]

/-- The compression variance is the compressed star square of the Lie
commutator. -/
theorem compression_variance_eq_commutator {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p * q * p - (p * q * p) * (p * q * p) =
      (p * star ⁅p, q⁆) * (⁅p, q⁆ * p) := by
  rw [compression_variance_eq_leakage hp hq]
  have hcomm := commutator_mul_projection (q := q) hp.isIdempotentElem
  have hstar : p * star ⁅p, q⁆ = -star ((1 - p) * q * p) := by
    calc
      _ = star (⁅p, q⁆ * p) := by
        rw [star_mul, hp.isSelfAdjoint.star_eq]
      _ = _ := by rw [hcomm, star_neg]
  rw [hstar, hcomm, neg_mul_neg]

end StarRing

section Ordered

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

/-- A compressed projection has nonnegative variance in a star-ordered ring. -/
theorem compression_variance_nonneg {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    0 ≤ p * q * p - (p * q * p) * (p * q * p) := by
  rw [compression_variance_eq_leakage hp hq]
  exact star_mul_self_nonneg _

/-- Projection compression is nonnegative in the native star order. -/
theorem compression_nonneg {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    0 ≤ p * q * p := by
  have hgram : star (q * p) * (q * p) = p * q * p := by
    simp only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    calc
      _ = p * (q * q) * p := by simp only [mul_assoc]
      _ = _ := by rw [hq.isIdempotentElem.eq]
  rw [← hgram]
  exact star_mul_self_nonneg _

/-- The retained projection bounds the compressed projection. -/
theorem compression_le_projection {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p * q * p ≤ p := by
  have h := compression_nonneg hp hq.one_sub
  have hdiff : p * (1 - q) * p = p - p * q * p := by
    noncomm_ring [hp.isIdempotentElem.eq]
  rw [hdiff] at h
  exact sub_nonneg.mp h

end Ordered

section CStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- The variance norm measures exactly the squared leakage norm. -/
theorem norm_compression_variance {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ‖p * q * p - (p * q * p) * (p * q * p)‖ =
      ‖(1 - p) * q * p‖ ^ 2 := by
  simpa only [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq] using
    InfoGeometry.Core.PeirceCompressionCStar.norm_compression_adjoint_square_defect
      p q hp.isIdempotentElem.eq hp.isSelfAdjoint.star_eq

/-- The same variance norm is the squared norm of the restricted commutator. -/
theorem norm_compression_variance_eq_commutator {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ‖p * q * p - (p * q * p) * (p * q * p)‖ = ‖⁅p, q⁆ * p‖ ^ 2 := by
  rw [norm_compression_variance hp hq,
    commutator_mul_projection hp.isIdempotentElem, norm_neg]

/-- In a C-star ring, a compressed projection remains idempotent exactly
when the original projections commute. -/
theorem compression_idempotent_iff_commute {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsIdempotentElem (p * q * p) ↔ Commute p q := by
  have h := InfoGeometry.Core.PeirceCompressionCStar.compression_square_eq_iff
    p q hp.isIdempotentElem.eq hp.isSelfAdjoint.star_eq hq.isSelfAdjoint.star_eq
  rw [hq.isIdempotentElem.eq] at h
  change (p * q * p) * (p * q * p) = p * q * p ↔ p * q = q * p
  exact eq_comm.trans h

end CStar

end InfoGeometry.OperatorAlgebra.ProjectionLocalization
