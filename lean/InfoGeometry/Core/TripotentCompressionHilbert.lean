/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentCompression
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The common kernel controlling tripotent compression positivity

The carrier is the algebra of bounded operators on an arbitrary real Hilbert
space. The star is the native Hilbert adjoint. No finite dimension, matrix
representation, or commutation of the state with the tripotent is assumed.

The two-channel ring factorization gives the exact quadratic form and kernel
of the compressed idempotency defect. Strict positivity on the observed
range is equivalent to absence of a common kernel vector in that range.
Nonzero channel operators alone do not supply this condition. Pointwise
strict positivity in an infinite-dimensional space is not a claim of a
uniform positive lower bound, invertibility, or a spectral gap.
-/

namespace InfoGeometry.Core.TripotentCompressionHilbert

open ContinuousLinearMap InfoGeometry.Physics.Algebra TripotentCompression

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The native Hilbert adjoint turns a sum of two operator squares into the
sum of the two exact outgoing energies. -/
theorem inner_gram_sum (a b : E →L[ℝ] E) (v : E) :
    inner ℝ v ((star a * a + star b * b) v) = ‖a v‖ ^ 2 + ‖b v‖ ^ 2 := by
  change inner ℝ v (adjoint a (a v) + adjoint b (b v)) = _
  rw [inner_add_right, adjoint_inner_right, adjoint_inner_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- Zero quadratic form detects both channels, not just one of them. -/
theorem inner_gram_sum_eq_zero_iff (a b : E →L[ℝ] E) (v : E) :
    inner ℝ v ((star a * a + star b * b) v) = 0 ↔ a v = 0 ∧ b v = 0 := by
  rw [inner_gram_sum, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _),
    sq_eq_zero_iff, sq_eq_zero_iff, norm_eq_zero, norm_eq_zero]

/-- The operator kernel and quadratic-form null space agree for this Gram sum. -/
theorem gram_sum_apply_eq_zero_iff (a b : E →L[ℝ] E) (v : E) :
    (star a * a + star b * b) v = 0 ↔ a v = 0 ∧ b v = 0 := by
  constructor
  · intro h
    apply (inner_gram_sum_eq_zero_iff a b v).mp
    rw [h, inner_zero_right]
  · rintro ⟨ha, hb⟩
    change adjoint a (a v) + adjoint b (b v) = 0
    simp only [ha, hb, map_zero, add_zero]

/-- The native submodule kernel is the intersection of the two native kernels. -/
theorem gram_sum_ker (a b : E →L[ℝ] E) :
    (star a * a + star b * b).ker = a.ker ⊓ b.ker := by
  ext v
  exact gram_sum_apply_eq_zero_iff a b v

variable {t x : E →L[ℝ] E}

/-- The compression defect measures the squared Hilbert norms of both
outgoing sectors. The projectors are the existing normalized spectral
polynomials in the same bounded operator `t`. -/
theorem inner_compression_defect
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) (v : E) :
    inner ℝ v ((projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t)) v) =
      ‖(projZero t * x * projPos t) v‖ ^ 2 +
        ‖(projNeg t * x * projPos t) v‖ ^ 2 := by
  rw [idempotent_compression_defect_eq_gram_sum ht hts hx hxs]
  exact inner_gram_sum _ _ v

/-- Hilbert positivity is supplied by the inner product, not by ring
idempotence alone. -/
theorem inner_compression_defect_nonneg
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) (v : E) :
    0 ≤ inner ℝ v ((projPos t * x * projPos t -
      (projPos t * x * projPos t) * (projPos t * x * projPos t)) v) := by
  rw [inner_compression_defect ht hts hx hxs]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The defect's quadratic form vanishes exactly on vectors invisible to both
outgoing channels. -/
theorem inner_compression_defect_eq_zero_iff
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) (v : E) :
    inner ℝ v ((projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t)) v) = 0 ↔
      (projZero t * x * projPos t) v = 0 ∧
        (projNeg t * x * projPos t) v = 0 := by
  rw [idempotent_compression_defect_eq_gram_sum ht hts hx hxs]
  exact inner_gram_sum_eq_zero_iff _ _ v

/-- The same common-kernel criterion controls annihilation by the operator. -/
theorem compression_defect_apply_eq_zero_iff
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) (v : E) :
    (projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t)) v = 0 ↔
      (projZero t * x * projPos t) v = 0 ∧
        (projNeg t * x * projPos t) v = 0 := by
  rw [idempotent_compression_defect_eq_gram_sum ht hts hx hxs]
  exact gram_sum_apply_eq_zero_iff _ _ v

/-- This kernel equality holds in arbitrary real Hilbert dimension. -/
theorem compression_defect_ker
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) :
    (projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t)).ker =
      (projZero t * x * projPos t).ker ⊓
        (projNeg t * x * projPos t).ker := by
  rw [idempotent_compression_defect_eq_gram_sum ht hts hx hxs]
  exact gram_sum_ker _ _

/-- The precise extra condition for strict positivity is joint injectivity of
the outgoing channels on the observed range. This is pointwise positivity;
there is no asserted uniform coercivity constant. -/
theorem compression_defect_strict_on_range_iff
    (ht : t * t * t = t) (hts : star t = t)
    (hx : x * x = x) (hxs : star x = x) :
    (∀ v ∈ (projPos t).range, v ≠ 0 →
      0 < inner ℝ v ((projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t)) v)) ↔
      (projPos t).range ⊓
        ((projZero t * x * projPos t).ker ⊓
          (projNeg t * x * projPos t).ker) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  constructor
  · intro h v hv
    by_contra hne
    have hpos := h v hv.1 hne
    have hzero := (inner_compression_defect_eq_zero_iff ht hts hx hxs v).mpr hv.2
    exact (ne_of_gt hpos) hzero
  · intro h v hv hne
    have hnonneg := inner_compression_defect_nonneg ht hts hx hxs v
    have hnotzero : inner ℝ v ((projPos t * x * projPos t -
        (projPos t * x * projPos t) * (projPos t * x * projPos t)) v) ≠ 0 := by
      intro hz
      apply hne
      exact h v ⟨hv, (inner_compression_defect_eq_zero_iff ht hts hx hxs v).mp hz⟩
    exact lt_of_le_of_ne hnonneg (Ne.symm hnotzero)

end InfoGeometry.Core.TripotentCompressionHilbert
