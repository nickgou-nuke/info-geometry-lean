/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionDefect
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Two-channel compression for the normalized tripotent projectors

The existing tripotent spectral polynomials resolve the complement of the
positive projector into the zero and negative projectors. Combining that
resolution with the owned Peirce compression identity retains the order of
both return channels. The star section gives Gram factorizations only;
ordered positivity and zero detection require additional structures.

The displayed defect is `rho - rho*rho`, the negative of the repository's
`IdempotencyDefect.defect rho`. Compression is not a partial trace and need
not produce a trace-one operator.
-/

namespace InfoGeometry.Core.TripotentCompression

open InfoGeometry.Physics.Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The complement of the positive projector is the sum of the other two
spectral polynomials, even before imposing tripotence. -/
theorem one_sub_projPos (t : A) :
    1 - projPos t = projZero t + projNeg t := by
  calc
    _ = (projPos t + projZero t + projNeg t) - projPos t := by
      rw [proj_sum_eq_id]
    _ = _ := by abel

/-- The multiplication defect resolves into the two ordered return channels.
The inputs are arbitrary and need not commute with one another or with `t`. -/
theorem compression_mul_defect_two_channels {t : A}
    (ht : t * t * t = t) (x y : A) :
    projPos t * (x * y) * projPos t -
        (projPos t * x * projPos t) * (projPos t * y * projPos t) =
      (projPos t * x * projZero t) * (projZero t * y * projPos t) +
        (projPos t * x * projNeg t) * (projNeg t * y * projPos t) := by
  rw [PeirceCompressionDefect.compression_mul_defect _ x y
    (projPos_idempotent ht), one_sub_projPos]
  calc
    _ = projPos t * x * (projZero t * projZero t) * y * projPos t +
        projPos t * x * (projNeg t * projNeg t) * y * projPos t := by
      rw [projZero_idempotent ht, projNeg_idempotent ht]
      noncomm_ring
    _ = _ := by simp only [mul_assoc]

/-- Compressing an idempotent leaves exactly the zero and negative return
channels. No star, norm, or positivity hypothesis is used. -/
theorem idempotent_compression_defect_two_channels {t x : A}
    (ht : t * t * t = t) (hx : x * x = x) :
    projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t) =
      (projPos t * x * projZero t) * (projZero t * x * projPos t) +
        (projPos t * x * projNeg t) * (projNeg t * x * projPos t) := by
  simpa only [hx] using compression_mul_defect_two_channels ht x x

/-- Resolving the outgoing transfer does not discard either exterior sector. -/
theorem complementary_transfer_eq_sum (t x : A) :
    (1 - projPos t) * x * projPos t =
      projZero t * x * projPos t + projNeg t * x * projPos t := by
  rw [one_sub_projPos, add_mul, add_mul]

/-- Orthogonality makes cancellation between the two outgoing channels
impossible. This statement is purely algebraic, with no positivity premise. -/
theorem complementary_transfer_eq_zero_iff {t : A}
    (ht : t * t * t = t) (x : A) :
    (1 - projPos t) * x * projPos t = 0 ↔
      projZero t * x * projPos t = 0 ∧ projNeg t * x * projPos t = 0 := by
  have hzero : projZero t * (1 - projPos t) = projZero t := by
    rw [mul_sub, mul_one, projZero_mul_projPos_eq_zero ht, sub_zero]
  have hneg : projNeg t * (1 - projPos t) = projNeg t := by
    rw [mul_sub, mul_one, projNeg_mul_projPos_eq_zero ht, sub_zero]
  constructor
  · intro h
    constructor
    · have h' := congrArg (fun z : A => projZero t * z) h
      simpa only [← mul_assoc, hzero, mul_zero] using h'
    · have h' := congrArg (fun z : A => projNeg t * z) h
      simpa only [← mul_assoc, hneg, mul_zero] using h'
  · rintro ⟨hzero', hneg'⟩
    rw [complementary_transfer_eq_sum, hzero', hneg', add_zero]

section Star

variable [StarRing A] [StarModule ℝ A]

/-- Polarization gives two mixed Gram products, with neither input assumed
self-adjoint. The intermediate projectors are the existing normalized ones. -/
theorem compression_adjoint_mul_two_channels {t : A}
    (ht : t * t * t = t) (hts : star t = t) (x y : A) :
    projPos t * (star x * y) * projPos t -
        (projPos t * star x * projPos t) * (projPos t * y * projPos t) =
      star (projZero t * x * projPos t) * (projZero t * y * projPos t) +
        star (projNeg t * x * projPos t) * (projNeg t * y * projPos t) := by
  rw [compression_mul_defect_two_channels ht]
  simp only [star_mul, star_projPos hts, star_projZero hts, star_projNeg hts,
    mul_assoc]

/-- A self-adjoint global idempotent gives a sum of two star-squares.
The formula is also valid in an indefinite star algebra, where positivity
and detection of zero by star-squares must not be inferred. -/
theorem idempotent_compression_defect_eq_gram_sum {t x : A}
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) :
    projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t) =
      star (projZero t * x * projPos t) * (projZero t * x * projPos t) +
        star (projNeg t * x * projPos t) * (projNeg t * x * projPos t) := by
  simpa only [hxs, hx] using compression_adjoint_mul_two_channels ht hts x x

/-- For self-adjoint data the outgoing and incoming channel vanish together. -/
theorem zero_channel_eq_zero_iff_reverse {t x : A}
    (hts : star t = t) (hxs : star x = x) :
    projZero t * x * projPos t = 0 ↔ projPos t * x * projZero t = 0 := by
  constructor <;> intro h <;>
    simpa only [star_mul, star_projPos hts, star_projZero hts, hxs,
      star_zero, mul_assoc] using congrArg star h

/-- The same reversal criterion holds for the negative channel. -/
theorem neg_channel_eq_zero_iff_reverse {t x : A}
    (hts : star t = t) (hxs : star x = x) :
    projNeg t * x * projPos t = 0 ↔ projPos t * x * projNeg t = 0 := by
  constructor <;> intro h <;>
    simpa only [star_mul, star_projPos hts, star_projNeg hts, hxs,
      star_zero, mul_assoc] using congrArg star h

end Star

end InfoGeometry.Core.TripotentCompression
