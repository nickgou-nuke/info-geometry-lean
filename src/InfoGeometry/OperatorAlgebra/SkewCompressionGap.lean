/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionCStar
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Square-first compression of a skew-adjoint operator

The difference between compressing `-a²` and squaring the compressed
skew-adjoint operator is a native Gram operator. The existing polarized
Peirce compression identity supplies the algebraic calculation. Its
complementary transfer corner measures the entire defect.

These are finite or abstract operator identities. They do not assert a
spectral gap for an arbitrary boundary truncation.
-/

namespace InfoGeometry.OperatorAlgebra.SkewCompressionGap

open InfoGeometry.Core.PeirceCompressionDefect
open InfoGeometry.Core.PeirceCompressionCStar

section Ring

variable {A : Type*} [Ring A]

/-- Centering both constructions by the same compressed operator leaves
exactly the negative exterior return. No commutation of the center is assumed. -/
theorem centered_negative_square_compression_defect (p a μ : A) (hp : p * p = p) :
    p * (-(a * a) - μ) * p -
        (-((p * a * p) * (p * a * p)) - p * μ * p) =
      -(p * a * (1 - p) * a * p) := by
  have h := compression_mul_defect p a a hp
  calc
    p * (-(a * a) - μ) * p -
        (-((p * a * p) * (p * a * p)) - p * μ * p) =
        -(p * (a * a) * p - (p * a * p) * (p * a * p)) := by
          noncomm_ring
    _ = -(p * a * (1 - p) * a * p) := congrArg Neg.neg h

/-- A unit square on the selected corner gives zero centered square-first
compression. This conclusion uses the square before the cut. -/
theorem centered_negative_square_eq_zero (p a : A) (hp : p * p = p)
    (hsquare : p * (a * a) * p = -p) :
    p * (-(a * a) - 1) * p = 0 := by
  calc
    p * (-(a * a) - 1) * p = -(p * (a * a) * p) - p * p := by
      noncomm_ring
    _ = 0 := by rw [hsquare, hp]; simp

variable [StarRing A]

/-- For skew-adjoint input, square-first minus truncate-first is exactly
the star-square of the outgoing complementary corner. -/
theorem negative_square_compression_defect_eq_gram (p a : A)
    (hp : p * p = p) (hps : star p = p) (has : star a = -a) :
    p * (-(a * a)) * p + (p * a * p) * (p * a * p) =
      star ((1 - p) * a * p) * ((1 - p) * a * p) := by
  simpa only [has, neg_mul, mul_neg, sub_neg_eq_add] using
    compression_adjoint_mul_defect p a a hp hps

/-- One vanishing transfer corner forces its adjoint corner to vanish.
For skew-adjoint input this is exactly commutation with the cut. -/
theorem skewAdjoint_transfer_zero_iff_commute (p a : A)
    (hp : p * p = p) (hps : star p = p) (has : star a = -a) :
    (1 - p) * a * p = 0 ↔ p * a = a * p := by
  constructor
  · intro hzero
    have hap : a * p = p * a * p := by
      apply sub_eq_zero.mp
      simpa only [sub_mul, one_mul] using hzero
    have hpa : p * a = p * a * p := by
      have hstar := congrArg star hap
      simpa only [star_mul, hps, has, mul_neg, neg_mul, mul_assoc, neg_inj] using hstar
    exact hpa.trans hap.symm
  · intro hcomm
    calc
      (1 - p) * a * p = a * p - p * (a * p) := by noncomm_ring
      _ = a * p - p * (p * a) := by rw [← hcomm]
      _ = 0 := by rw [← mul_assoc, hp, hcomm, sub_self]

end Ring

section CStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- The defect norm is precisely the squared transfer norm; no matrix
norm convention or finite-dimensional representation is needed. -/
theorem norm_negative_square_compression_defect (p a : A)
    (hp : p * p = p) (hps : star p = p) (has : star a = -a) :
    ‖p * (-(a * a)) * p + (p * a * p) * (p * a * p)‖ =
      ‖(1 - p) * a * p‖ ^ 2 := by
  simpa only [has, neg_mul, mul_neg, sub_neg_eq_add] using
    norm_compression_adjoint_square_defect p a hp hps

/-- The two orders of square and cut agree exactly when no complementary
transfer remains. Properness comes from the native C-star structure. -/
theorem negative_square_compression_defect_eq_zero_iff_transfer (p a : A)
    (hp : p * p = p) (hps : star p = p) (has : star a = -a) :
    p * (-(a * a)) * p + (p * a * p) * (p * a * p) = 0 ↔
      (1 - p) * a * p = 0 := by
  rw [negative_square_compression_defect_eq_gram p a hp hps has]
  exact CStarRing.star_mul_self_eq_zero_iff _

/-- A skew-adjoint operator has zero square-compression defect precisely
when it commutes with the projection. -/
theorem negative_square_compression_defect_eq_zero_iff_commute (p a : A)
    (hp : p * p = p) (hps : star p = p) (has : star a = -a) :
    p * (-(a * a)) * p + (p * a * p) * (p * a * p) = 0 ↔
      p * a = a * p := by
  exact (negative_square_compression_defect_eq_zero_iff_transfer p a hp hps has).trans
    (skewAdjoint_transfer_zero_iff_commute p a hp hps has)

end CStar

section Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

/-- In a full finite matrix algebra, the exterior return contributes a
positive semidefinite operator to square-first compression. -/
theorem negative_square_compression_defect_posSemidef (p a : Matrix ι ι R)
    (hp : p * p = p) (hps : star p = p) (has : star a = -a) :
    (p * (-(a * a)) * p + (p * a * p) * (p * a * p)).PosSemidef := by
  rw [negative_square_compression_defect_eq_gram p a hp hps has]
  exact Matrix.posSemidef_conjTranspose_mul_self ((1 - p) * a * p)

end Matrix

end InfoGeometry.OperatorAlgebra.SkewCompressionGap
