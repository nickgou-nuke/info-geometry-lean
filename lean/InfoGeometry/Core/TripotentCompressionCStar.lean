/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentCompression
import InfoGeometry.Core.PeirceCompressionCStar
import Mathlib.Algebra.Order.Star.Basic

/-!
# Positivity and exact zero criteria for tripotent compression

Star-compatible order yields nonnegativity. The separate native C-star norm
structure detects zero and measures the full transfer. These assumptions do
not assert positive definiteness, invertibility, a logarithm, a trace-one
state, or a nontrivial modular flow. All results are dimension-free.
-/

namespace InfoGeometry.Core.TripotentCompressionCStar

open InfoGeometry.Physics.Algebra
open TripotentCompression

section Ordered

variable {A : Type*} [Ring A] [Algebra ℝ A]
  [StarRing A] [StarModule ℝ A] [PartialOrder A] [StarOrderedRing A]

/-- The compression defect is nonnegative in a star-ordered ring.
Nonnegative is the only order conclusion: it need not be invertible. -/
theorem idempotent_compression_defect_nonneg {t x : A}
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) :
    0 ≤ projPos t * x * projPos t -
      (projPos t * x * projPos t) * (projPos t * x * projPos t) := by
  rw [idempotent_compression_defect_eq_gram_sum ht hts hx hxs]
  exact add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _)

end Ordered

section CStar

variable {A : Type*} [NormedRing A] [Algebra ℝ A]
  [StarRing A] [StarModule ℝ A] [CStarRing A]

/-- Exact size of the defect of a compressed self-adjoint idempotent.
The right hand side retains both outgoing channels as operators. -/
theorem norm_idempotent_compression_defect {t x : A}
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) :
    ‖projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t)‖ =
      ‖projZero t * x * projPos t + projNeg t * x * projPos t‖ ^ 2 := by
  simpa only [hxs, hx, complementary_transfer_eq_sum] using
    PeirceCompressionCStar.norm_compression_adjoint_square_defect
      (projPos t) x (projPos_idempotent ht) (star_projPos hts)

/-- C-star properness detects the simultaneous vanishing of both channels. -/
theorem idempotent_compression_defect_eq_zero_iff {t x : A}
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) :
    projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t) = 0 ↔
      projZero t * x * projPos t = 0 ∧ projNeg t * x * projPos t = 0 := by
  rw [sub_eq_zero]
  have h := PeirceCompressionCStar.compression_adjoint_square_eq_iff
    (projPos t) x (projPos_idempotent ht) (star_projPos hts)
  rw [hxs, hx] at h
  exact h.trans (complementary_transfer_eq_zero_iff ht x)

/-- The observed compression is an idempotent exactly when the global
self-adjoint idempotent commutes with the observing projector. -/
theorem compression_idempotent_iff_commute {t x : A}
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) :
    IsIdempotentElem (projPos t * x * projPos t) ↔
      projPos t * x = x * projPos t := by
  have h := PeirceCompressionCStar.compression_square_eq_iff
    (projPos t) x (projPos_idempotent ht) (star_projPos hts) hxs
  rw [hx] at h
  exact eq_comm.trans h

/-- Either nonzero outgoing channel forces a nonzero compression defect;
this is not a claim of positive definiteness. -/
theorem idempotent_compression_defect_ne_zero_iff {t x : A}
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) :
    projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t) ≠ 0 ↔
      projZero t * x * projPos t ≠ 0 ∨ projNeg t * x * projPos t ≠ 0 := by
  rw [ne_eq, idempotent_compression_defect_eq_zero_iff ht hts hx hxs]
  exact not_and_or

end CStar

end InfoGeometry.Core.TripotentCompressionCStar
