/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ProjectionLocalization
import InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
import InfoGeometry.Algebra.NonCommutativeIsometry
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Star.StarRingHom

/-!
# Isometric compression and the range corner

A one-sided isometry `v` in an arbitrary associative star ring gives a native
non-unital star-ring embedding `x ↦ v * x * star v`. Its range is the genuine
unital corner of `v * star v`, and the explicit corner ring equivalence has
inverse `x ↦ star v * x * v`.

This algebraic construction does not identify `v` with a particular integral
transform. In C-star rings, the embedding preserves norms and identifies the
norms of compressed operators and their range-corner representatives. A
projection compresses to a projection exactly under the stated compatibility
condition; one-sided isometry alone does not ensure that conclusion.
-/

namespace InfoGeometry.OperatorAlgebra.IsometryCornerLocalization

open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
open InfoGeometry.Algebra.NonCommutativity

section StarRing

variable {A : Type*} [Ring A] [StarRing A]

/-- One-sided isometry is sufficient for its range operator to be a star
projection. The reverse identity `v * star v = 1` is not assumed. -/
theorem rangeProjection_isStarProjection {v : A} (hv : star v * v = 1) :
    IsStarProjection (rangeProjection v) where
  isIdempotentElem := by
    apply rangeProjection_idempotent_of_partial_isometry
    rw [mul_assoc, hv, mul_one]
  isSelfAdjoint := by simp [rangeProjection]

/-- The existing associative conjugation is bundled as a native non-unital
star-ring homomorphism. It is unital precisely when `v * star v = 1`. -/
def isometryEmbedding {v : A} (hv : star v * v = 1) : A →⋆ₙ+* A where
  toFun := unitaryConjugation v
  map_zero' := by simp [unitaryConjugation]
  map_add' x y := by simp only [unitaryConjugation, mul_add, add_mul]
  map_mul' x y := unitaryConjugation_mul hv x y
  map_star' x := by simp [unitaryConjugation, star_mul, mul_assoc]

/-- Pull an ambient operator back through an isometry. This is additive but
need not preserve ambient multiplication. -/
def compression (v : A) : A →+ A where
  toFun x := star v * x * v
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, add_mul]

@[simp] theorem isometryEmbedding_apply {v : A} (hv : star v * v = 1) (x : A) :
    isometryEmbedding hv x = v * x * star v := rfl

@[simp] theorem compression_apply (v x : A) :
    compression v x = star v * x * v := rfl

/-- Pullback is a left inverse to the star-ring embedding. -/
theorem compression_embedding {v : A} (hv : star v * v = 1) (x : A) :
    compression v (isometryEmbedding hv x) = x := by
  change star v * (v * x * star v) * v = x
  calc
    _ = (star v * v) * x * (star v * v) := by simp only [mul_assoc]
    _ = x := by rw [hv, one_mul, mul_one]

/-- The star-ring embedding is faithful. -/
theorem isometryEmbedding_injective {v : A} (hv : star v * v = 1) :
    Function.Injective (isometryEmbedding hv) := by
  intro x y hxy
  have h := congrArg (compression v) hxy
  simpa only [compression_embedding hv] using h

private theorem rangeProjection_mul_embedding {v : A}
    (hv : star v * v = 1) (x : A) :
    rangeProjection v * isometryEmbedding hv x = isometryEmbedding hv x := by
  change (v * star v) * (v * x * star v) = v * x * star v
  calc
    _ = v * (star v * v) * x * star v := by simp only [mul_assoc]
    _ = _ := by rw [hv, mul_one]

private theorem embedding_mul_rangeProjection {v : A}
    (hv : star v * v = 1) (x : A) :
    isometryEmbedding hv x * rangeProjection v = isometryEmbedding hv x := by
  change (v * x * star v) * (v * star v) = v * x * star v
  calc
    _ = v * x * (star v * v) * star v := by simp only [mul_assoc]
    _ = _ := by rw [hv, mul_one]

/-- The operator algebra is explicitly isomorphic to the native range corner.
The identity of the target ring is `v * star v`, not the ambient identity. -/
def isometryCornerEquiv {v : A} (hv : star v * v = 1) :
    A ≃+* (rangeProjection_isStarProjection hv).isIdempotentElem.Corner where
  toFun x := ⟨isometryEmbedding hv x, by
    apply (Subsemigroup.mem_corner_iff
      (rangeProjection_isStarProjection hv).isIdempotentElem).mpr
    exact ⟨rangeProjection_mul_embedding hv x, embedding_mul_rangeProjection hv x⟩⟩
  invFun x := compression v x.val
  left_inv x := compression_embedding hv x
  right_inv x := by
    apply Subtype.ext
    have hx := (Subsemigroup.mem_corner_iff
      (rangeProjection_isStarProjection hv).isIdempotentElem).mp x.property
    change v * (star v * x.val * v) * star v = x.val
    calc
      _ = rangeProjection v * x.val * rangeProjection v := by
        simp only [rangeProjection, mul_assoc]
      _ = x.val := by rw [hx.1, hx.2]
  map_add' x y := Subtype.ext (map_add (isometryEmbedding hv) x y)
  map_mul' x y := Subtype.ext (map_mul (isometryEmbedding hv) x y)

/-- The corner equivalence preserves the ambient star operation. -/
theorem isometryCornerEquiv_star {v : A} (hv : star v * v = 1) (x : A) :
    (isometryCornerEquiv hv (star x)).val = star (isometryCornerEquiv hv x).val :=
  map_star (isometryEmbedding hv) x

/-- Embedding a pulled-back operator gives its compression to the range corner. -/
theorem embedding_compression {v : A} (hv : star v * v = 1) (s : A) :
    isometryEmbedding hv (compression v s) =
      rangeProjection v * s * rangeProjection v := by
  simp only [isometryEmbedding_apply, compression_apply, rangeProjection, mul_assoc]

/-- The original isometry intertwines pullback with range-corner compression. -/
theorem isometry_intertwines {v : A} (hv : star v * v = 1) (s : A) :
    v * compression v s = (rangeProjection v * s * rangeProjection v) * v := by
  change v * (star v * s * v) = ((v * star v) * s * (v * star v)) * v
  calc
    _ = v * star v * s * v * 1 := by simp only [mul_one, mul_assoc]
    _ = v * star v * s * v * (star v * v) := by rw [hv]
    _ = _ := by simp only [mul_assoc]

/-- Pullback is unchanged by compressing the symbol to the range corner. -/
theorem compression_range_corner {v : A} (hv : star v * v = 1) (s : A) :
    compression v (rangeProjection v * s * rangeProjection v) = compression v s := by
  rw [← embedding_compression hv s, compression_embedding hv]

/-- Pullback respects star, even for symbols that are not self-adjoint. -/
theorem compression_star (v s : A) :
    compression v (star s) = star (compression v s) := by
  simp only [compression_apply, star_mul, star_star, mul_assoc]

/-- Complementary ambient symbols sum to the identity after pullback. -/
theorem compression_complement_partition {v : A} (hv : star v * v = 1) (s : A) :
    compression v s + compression v (1 - s) = 1 := by
  have hs : s + (1 - s) = 1 := by rw [add_comm, sub_add_cancel]
  rw [← map_add, hs, compression_apply, mul_one, hv]

/-- The complementary range-corner operators sum to the corner identity. -/
theorem range_corner_complement_partition {v : A} (hv : star v * v = 1) (s : A) :
    rangeProjection v * s * rangeProjection v +
      rangeProjection v * (1 - s) * rangeProjection v = rangeProjection v := by
  have hp := (rangeProjection_isStarProjection hv).isIdempotentElem.eq
  noncomm_ring [hp]

/-- A non-unital embedding preserves every positive power. The zero power
would map to the corner identity rather than to the ambient identity. -/
theorem embedding_pow_succ {v : A} (hv : star v * v = 1) (x : A) (n : ℕ) :
    isometryEmbedding hv (x ^ (n + 1)) = (isometryEmbedding hv x) ^ (n + 1) := by
  induction n with
  | zero => simp only [Nat.zero_add, pow_one]
  | succ n ih =>
    calc
      _ = isometryEmbedding hv (x ^ (n + 1) * x) := by rw [pow_succ]
      _ = isometryEmbedding hv (x ^ (n + 1)) * isometryEmbedding hv x := map_mul _ _ _
      _ = (isometryEmbedding hv x) ^ (n + 1) * isometryEmbedding hv x := by rw [ih]
      _ = _ := (pow_succ _ _).symm

/-- Positive powers intertwine in the ambient algebra. -/
theorem range_corner_pow_succ {v : A} (hv : star v * v = 1) (s : A) (n : ℕ) :
    v * (compression v s) ^ (n + 1) * star v =
      (rangeProjection v * s * rangeProjection v) ^ (n + 1) := by
  change isometryEmbedding hv ((compression v s) ^ (n + 1)) = _
  rw [embedding_pow_succ hv, embedding_compression hv]

/-- Pulling powers back through the isometry works also at exponent zero. -/
theorem compression_pow {v : A} (hv : star v * v = 1) (s : A) (n : ℕ) :
    (compression v s) ^ n =
      compression v ((rangeProjection v * s * rangeProjection v) ^ n) := by
  cases n with
  | zero => simpa only [pow_zero, compression_apply, mul_one] using hv.symm
  | succ n =>
    calc
      _ = compression v (isometryEmbedding hv ((compression v s) ^ (n + 1))) :=
        (compression_embedding hv _).symm
      _ = _ := by rw [embedding_pow_succ hv, embedding_compression hv]

end StarRing

section CStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- Left multiplication by an algebraic isometry preserves the C-star norm. -/
theorem norm_isometry_mul {v : A} (hv : star v * v = 1) (x : A) :
    ‖v * x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖v * x‖ ^ 2 = ‖star (v * x) * (v * x)‖ := by
      rw [CStarRing.norm_star_mul_self, pow_two]
    _ = ‖star x * (star v * v) * x‖ := by
      simp only [star_mul, mul_assoc]
    _ = ‖star x * x‖ := by rw [hv, mul_one]
    _ = ‖x‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]

/-- Right multiplication by the adjoint of an isometry preserves the norm. -/
theorem norm_mul_star_isometry {v : A} (hv : star v * v = 1) (x : A) :
    ‖x * star v‖ = ‖x‖ := by
  calc
    _ = ‖star (x * star v)‖ := (norm_star _).symm
    _ = ‖v * star x‖ := by rw [star_mul, star_star]
    _ = ‖star x‖ := norm_isometry_mul hv _
    _ = ‖x‖ := norm_star _

/-- The native star-ring embedding preserves the ambient C-star norm. -/
theorem norm_isometryEmbedding {v : A} (hv : star v * v = 1) (x : A) :
    ‖isometryEmbedding hv x‖ = ‖x‖ := by
  rw [isometryEmbedding_apply, norm_mul_star_isometry hv, norm_isometry_mul hv]

/-- Pullback and range-corner compression have equal operator-algebra norms. -/
theorem norm_compression_eq_range_corner {v : A} (hv : star v * v = 1) (s : A) :
    ‖compression v s‖ = ‖rangeProjection v * s * rangeProjection v‖ := by
  rw [← embedding_compression hv s, norm_isometryEmbedding hv]

/-- The norm equality extends to all powers, with exponent zero handled in
the ambient algebra on both sides. -/
theorem norm_compression_pow_eq_range_corner_pow {v : A}
    (hv : star v * v = 1) (s : A) (n : ℕ) :
    ‖(compression v s) ^ n‖ =
      ‖(rangeProjection v * s * rangeProjection v) ^ n‖ := by
  cases n with
  | zero => simp only [pow_zero]
  | succ n =>
    rw [← range_corner_pow_succ hv s n, norm_mul_star_isometry hv,
      norm_isometry_mul hv]

/-- Pullback of a projection is idempotent exactly when the projection
commutes with the isometry's range projection. -/
theorem compression_projection_idempotent_iff {v q : A}
    (hv : star v * v = 1) (hq : IsStarProjection q) :
    IsIdempotentElem (compression v q) ↔ Commute (rangeProjection v) q := by
  have hmap : IsIdempotentElem (compression v q) ↔
      IsIdempotentElem (rangeProjection v * q * rangeProjection v) := by
    change (compression v q) * (compression v q) = compression v q ↔
      (rangeProjection v * q * rangeProjection v) *
        (rangeProjection v * q * rangeProjection v) =
          rangeProjection v * q * rangeProjection v
    rw [← embedding_compression hv q, ← map_mul (isometryEmbedding hv)]
    exact (isometryEmbedding_injective hv).eq_iff.symm
  exact hmap.trans (ProjectionLocalization.compression_idempotent_iff_commute
    (rangeProjection_isStarProjection hv) hq)

/-- Because pullback preserves self-adjointness, the same compatibility
condition characterizes preservation of a native star projection. -/
theorem compression_isStarProjection_iff {v q : A}
    (hv : star v * v = 1) (hq : IsStarProjection q) :
    IsStarProjection (compression v q) ↔ Commute (rangeProjection v) q := by
  constructor
  · intro h
    exact (compression_projection_idempotent_iff hv hq).mp h.isIdempotentElem
  · intro h
    refine ⟨(compression_projection_idempotent_iff hv hq).mpr h, ?_⟩
    change star (compression v q) = compression v q
    rw [← compression_star, hq.isSelfAdjoint.star_eq]

end CStar

end InfoGeometry.OperatorAlgebra.IsometryCornerLocalization
