/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Singular.MoorePenroseSectors
import InfoGeometry.Algebra.PeirceRegularityIdentities

/-!
# Square-zero Moore-Penrose pairs

Use the repository's four Penrose equations and Mathlib `IsStarProjection`.
Square-zero forces support orthogonality, so the general commuting-sector
hypothesis is discharged here. The reciprocal sum `a+b` is tripotent, but
is NOT asserted self-adjoint: an MP inverse need not equal the adjoint.
-/
namespace InfoGeometry.Singular.MoorePenroseSquareZero

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenroseSectors
open InfoGeometry.Algebra.PeirceRegularityIdentities

variable {R : Type*} [Ring R] [StarRing R] {a b : R}

/-- Vanishing ordered overlap is equivalent to square-zero, not just implied by it. -/
theorem square_zero_iff_corange_range_zero (h : IsMoorePenroseInverse a b) :
    a * a = 0 ↔ (b * a) * (a * b) = 0 := by
  constructor
  · intro ha
    calc
      (b * a) * (a * b) = b * (a * a) * b := by simp only [mul_assoc]
      _ = 0 := by rw [ha]; simp
  · intro hz
    calc
      a * a = (a * b * a) * (a * b * a) := by rw [h.aba_eq_a]
      _ = a * ((b * a) * (a * b)) * a := by simp only [mul_assoc]
      _ = 0 := by rw [hz]; simp

/-- The reverse ordered overlap vanishes by taking star. -/
theorem supports_orthogonal (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    (a * b) * (b * a) = 0 ∧ (b * a) * (a * b) = 0 := by
  have hqp := (square_zero_iff_corange_range_zero h).mp ha
  have hpq : (a * b) * (b * a) = 0 := by
    have hs := congrArg star hqp
    rw [star_mul, h.ab_adj_eq, h.ba_adj_eq, star_zero] at hs
    exact hs
  exact ⟨hpq, hqp⟩

/-- The Moore-Penrose inverse of a square-zero element is square-zero. -/
theorem inverse_square_zero (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    b * b = 0 := by
  have hpq := (supports_orthogonal h ha).1
  calc
    b * b = (b * a * b) * (b * a * b) := by rw [h.bab_eq_b]
    _ = b * ((a * b) * (b * a)) * b := by simp only [mul_assoc]
    _ = 0 := by rw [hpq]; simp

/-- The active support and its common-null complement are native star projections. -/
theorem active_and_null_projections (h : IsMoorePenroseInverse a b)
    (ha : a * a = 0) :
    IsStarProjection (a * b + b * a) ∧ IsStarProjection (1 - (a * b + b * a)) := by
  obtain ⟨hp, hq⟩ := support_isStarProjection h
  have hs := hp.add hq (supports_orthogonal h ha).1
  exact ⟨hs, hs.one_sub⟩

/-- Three native self-adjoint idempotents; this does not assert that a+b is self-adjoint. -/
theorem three_star_projections (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    IsStarProjection (a * b) ∧ IsStarProjection (b * a) ∧
      IsStarProjection (1 - (a * b + b * a)) :=
  ⟨(support_isStarProjection h).1, (support_isStarProjection h).2,
    (active_and_null_projections h ha).2⟩

/-- All six ordered cross-products vanish. -/
theorem three_pairwise_zero (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    (a * b) * (b * a) = 0 ∧ (b * a) * (a * b) = 0 ∧
    (a * b) * (1 - (a * b + b * a)) = 0 ∧
    (1 - (a * b + b * a)) * (a * b) = 0 ∧
    (b * a) * (1 - (a * b + b * a)) = 0 ∧
    (1 - (a * b + b * a)) * (b * a) = 0 := by
  obtain ⟨hpq, hqp⟩ := supports_orthogonal h ha
  have hp : (a * b) * (a * b) = a * b := (support_isStarProjection h).1.isIdempotentElem
  have hq : (b * a) * (b * a) = b * a := (support_isStarProjection h).2.isIdempotentElem
  refine ⟨hpq, hqp, ?_, ?_, ?_, ?_⟩ <;> noncomm_ring [hp, hq, hpq, hqp]

/-- The common-null projector annihilates both elements in both orders. -/
theorem null_annihilates (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    a * (1 - (a * b + b * a)) = 0 ∧
    (1 - (a * b + b * a)) * a = 0 ∧
    b * (1 - (a * b + b * a)) = 0 ∧
    (1 - (a * b + b * a)) * b = 0 := by
  have hb := inverse_square_zero h ha
  have hab := h.aba_eq_a
  have hba := h.bab_eq_b
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring [ha, hb, hab, hba]

/-- The reciprocal sum squares to the active support. -/
theorem sum_square (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    (a + b) * (a + b) = a * b + b * a := by
  have hb := inverse_square_zero h ha
  noncomm_ring [ha, hb]

/-- The grading squares to the same active support. -/
theorem grading_square (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    (a * b - b * a) * (a * b - b * a) = a * b + b * a := by
  obtain ⟨hpq, hqp⟩ := supports_orthogonal h ha
  have hp : (a * b) * (a * b) = a * b := (support_isStarProjection h).1.isIdempotentElem
  have hq : (b * a) * (b * a) = b * a := (support_isStarProjection h).2.isIdempotentElem
  noncomm_ring [hp, hq, hpq, hqp]

/-- Tripotence holds over arbitrary characteristic; no division by two is used. -/
theorem grading_cube (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    (a * b - b * a) * (a * b - b * a) * (a * b - b * a) = a * b - b * a :=
  orthogonal_difference_cube (support_isStarProjection h).1.isIdempotentElem
    (support_isStarProjection h).2.isIdempotentElem
    (supports_orthogonal h ha).1 (supports_orthogonal h ha).2

/-- Left and right grading actions have opposite signs. -/
theorem grading_actions (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    (a * b - b * a) * a = a ∧ a * (a * b - b * a) = -a ∧
    (a * b - b * a) * b = -b ∧ b * (a * b - b * a) = b := by
  have hb := inverse_square_zero h ha
  have hab := h.aba_eq_a
  have hba := h.bab_eq_b
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring [ha, hb, hab, hba]

/-- Anticommutation of the grading and reciprocal sum. -/
theorem grading_anticommutes_sum (h : IsMoorePenroseInverse a b)
    (ha : a * a = 0) :
    (a * b - b * a) * (a + b) + (a + b) * (a * b - b * a) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := grading_actions h ha
  rw [mul_add, add_mul, h1, h2, h3, h4]
  abel

/-- The reciprocal sum is itself tripotent; self-adjointness is a separate question. -/
theorem sum_cube (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    (a + b) * (a + b) * (a + b) = a + b := by
  rw [sum_square h ha]
  have hb := inverse_square_zero h ha
  have hab := h.aba_eq_a
  have hba := h.bab_eq_b
  noncomm_ring [ha, hb, hab, hba]

/-- Square-zero specialization of the unnormalized Jordan associator. -/
theorem repeated_associator (h : IsMoorePenroseInverse a b) (ha : a * a = 0) :
    ((a * a + a * a) * b + b * (a * a + a * a)) -
      (a * (a * b + b * a) + (a * b + b * a) * a) = -(2 • a) := by
  rw [two_smul]
  have hab := h.aba_eq_a
  noncomm_ring [ha, hab]

/-- Higher-order overlap is an exact identity, without assuming square-zero. -/
theorem general_overlap_defect (h : IsMoorePenroseInverse a b) :
    (a * b + b * a) - (a * b - b * a) * (a * b - b * a) =
      (a * b) * (b * a) + (b * a) * (a * b) :=
  idempotent_overlap_defect (support_isStarProjection h).1.isIdempotentElem
    (support_isStarProjection h).2.isIdempotentElem

end InfoGeometry.Singular.MoorePenroseSquareZero
