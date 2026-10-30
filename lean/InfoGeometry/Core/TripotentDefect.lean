/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotencyDefect
import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Defects of the normalized tripotent projectors

The existing three projectors are polynomial expressions in an arbitrary
element of a real associative algebra. Their failures of orthogonality and
idempotence are exact multiples of `t * t * t - t`. No commutativity of the
ambient algebra is assumed.
-/

namespace InfoGeometry.Core.TripotentDefect

open IdempotencyDefect InfoGeometry.Physics.Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Opposite projectors are orthogonal precisely up to the quartic defect. -/
theorem projPos_mul_projNeg (t : A) :
    projPos t * projNeg t = (1 / 4 : ℝ) • (t * (t * t * t - t)) := by
  calc
    _ = (1 / 4 : ℝ) • ((t * t + t) * (t * t - t)) := by
      simp only [projPos, projNeg, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_smul]
      norm_num
    _ = _ := by congr 1; noncomm_ring

theorem projZero_mul_projPos (t : A) :
    projZero t * projPos t = (-1 / 2 : ℝ) • ((t * t * t - t) * (t + 1)) := by
  calc
    _ = (1 / 2 : ℝ) • ((1 - t * t) * (t * t + t)) := by
      rw [projZero, projPos, Algebra.mul_smul_comm]
    _ = (1 / 2 : ℝ) • (-((t * t * t - t) * (t + 1))) := by
      congr 1
      noncomm_ring
    _ = _ := by simp only [smul_neg, neg_div, neg_smul]

theorem projZero_mul_projNeg (t : A) :
    projZero t * projNeg t = (1 / 2 : ℝ) • ((t * t * t - t) * (1 - t)) := by
  calc
    _ = (1 / 2 : ℝ) • ((1 - t * t) * (t * t - t)) := by
      rw [projZero, projNeg, Algebra.mul_smul_comm]
    _ = _ := by congr 1; noncomm_ring

theorem defect_projPos (t : A) :
    defect (projPos t) = (1 / 4 : ℝ) • ((t + 2) * (t * t * t - t)) := by
  have h : (t * t + t) * (t * t + t) =
      (t + 2) * (t * t * t - t) + (2 : ℝ) • (t * t + t) := by
    rw [two_smul ℝ]
    noncomm_ring
  calc
    _ = (1 / 4 : ℝ) • ((t * t + t) * (t * t + t)) -
        (1 / 2 : ℝ) • (t * t + t) := by
      simp only [defect, projPos, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_smul]
      norm_num
    _ = _ := by
      rw [h, smul_add, smul_smul]
      norm_num

theorem defect_projNeg (t : A) :
    defect (projNeg t) = (1 / 4 : ℝ) • ((t - 2) * (t * t * t - t)) := by
  have h : (t * t - t) * (t * t - t) =
      (t - 2) * (t * t * t - t) + (2 : ℝ) • (t * t - t) := by
    rw [two_smul ℝ]
    noncomm_ring
  calc
    _ = (1 / 4 : ℝ) • ((t * t - t) * (t * t - t)) -
        (1 / 2 : ℝ) • (t * t - t) := by
      simp only [defect, projNeg, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_smul]
      norm_num
    _ = _ := by
      rw [h, smul_add, smul_smul]
      norm_num

omit [Algebra ℝ A] in
/-- The sign is positive: `(1 - t²)² - (1 - t²) = t (t³ - t)`. -/
theorem defect_projZero (t : A) :
    defect (projZero t) = t * (t * t * t - t) := by
  simp only [defect, projZero]
  noncomm_ring

variable {p q : A}

/-- The positive normalized projector recovers the first orthogonal idempotent. -/
theorem projPos_sub_of_orthogonal
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0) :
    projPos (p - q) = p := by
  rw [projPos, (IdempotentCartan.orthogonal_difference_powers hp hq hpq hqp).1]
  have h : p + q + (p - q) = (2 : ℝ) • p := by rw [two_smul ℝ]; abel
  rw [h, smul_smul]
  norm_num

/-- The negative normalized projector recovers the second orthogonal idempotent. -/
theorem projNeg_sub_of_orthogonal
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0) :
    projNeg (p - q) = q := by
  rw [projNeg, (IdempotentCartan.orthogonal_difference_powers hp hq hpq hqp).1]
  have h : p + q - (p - q) = (2 : ℝ) • q := by rw [two_smul ℝ]; abel
  rw [h, smul_smul]
  norm_num

omit [Algebra ℝ A] in
/-- The zero projector is the complementary third sector. -/
theorem projZero_sub_of_orthogonal
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0) :
    projZero (p - q) = 1 - p - q := by
  rw [projZero, (IdempotentCartan.orthogonal_difference_powers hp hq hpq hqp).1]
  abel

end InfoGeometry.Core.TripotentDefect
