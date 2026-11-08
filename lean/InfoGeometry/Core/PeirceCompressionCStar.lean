/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionDefect
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Compression equality and defect norm in C-star rings

The associative identities remain in `PeirceCompressionDefect`. Here the
native C-star norm identity detects zero transfer and measures its size.
No finite-dimensional, commutativity, or completeness assumption is used.
-/

namespace InfoGeometry.Core.PeirceCompressionCStar

open PeirceCompressionDefect

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- The compressed star-square defect has exactly the squared norm of the
complementary transfer corner, including for non-self-adjoint inputs. -/
theorem norm_compression_adjoint_square_defect (p x : A)
    (hp : p * p = p) (hps : star p = p) :
    ‖p * (star x * x) * p - (p * star x * p) * (p * x * p)‖ =
      ‖(1 - p) * x * p‖ ^ 2 := by
  rw [compression_adjoint_mul_defect p x x hp hps,
    CStarRing.norm_star_mul_self, pow_two]

/-- A mixed compression defect is bounded by the two transfer norms;
neither input is assumed self-adjoint. -/
theorem norm_compression_adjoint_mul_defect_le (p x y : A)
    (hp : p * p = p) (hps : star p = p) :
    ‖p * (star x * y) * p - (p * star x * p) * (p * y * p)‖ ≤
      ‖(1 - p) * x * p‖ * ‖(1 - p) * y * p‖ := by
  rw [compression_adjoint_mul_defect p x y hp hps]
  simpa only [norm_star] using
    norm_mul_le (star ((1 - p) * x * p)) ((1 - p) * y * p)

/-- Cauchy--Schwarz for compression defects in an arbitrary C-star ring. -/
theorem norm_compression_adjoint_mul_defect_sq_le (p x y : A)
    (hp : p * p = p) (hps : star p = p) :
    ‖p * (star x * y) * p - (p * star x * p) * (p * y * p)‖ ^ 2 ≤
      ‖p * (star x * x) * p - (p * star x * p) * (p * x * p)‖ *
      ‖p * (star y * y) * p - (p * star y * p) * (p * y * p)‖ := by
  rw [norm_compression_adjoint_square_defect p x hp hps,
    norm_compression_adjoint_square_defect p y hp hps]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (norm_compression_adjoint_mul_defect_le p x y hp hps) 2

/-- Native C-star properness supplies the exact zero-transfer criterion. -/
theorem compression_adjoint_square_eq_iff (p x : A)
    (hp : p * p = p) (hps : star p = p) :
    p * (star x * x) * p = (p * star x * p) * (p * x * p) ↔
      (1 - p) * x * p = 0 := by
  exact compression_adjoint_square_eq_iff_transfer_zero
    (fun z => (CStarRing.star_mul_self_eq_zero_iff z).mp) p x hp hps

/-- For a self-adjoint input, equality is exactly commutation with the
projection; properness is discharged by the native C-star structure. -/
theorem compression_square_eq_iff (p x : A)
    (hp : p * p = p) (hps : star p = p) (hxs : star x = x) :
    p * (x * x) * p = (p * x * p) * (p * x * p) ↔ p * x = x * p := by
  exact compression_square_eq_iff_commute
    (fun z => (CStarRing.star_mul_self_eq_zero_iff z).mp) p x hp hps hxs

end InfoGeometry.Core.PeirceCompressionCStar
