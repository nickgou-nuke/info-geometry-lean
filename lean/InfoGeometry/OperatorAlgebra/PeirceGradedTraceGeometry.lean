/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceGradedDifferential
import InfoGeometry.OperatorAlgebra.PeircePairPositivity

/-!
# Trace-adjoint geometry of the reflection-graded differential

For a star projection and an odd matrix, the trace-pairing adjoint of the
minus-sign twisted action has a plus sign. Their symmetric composition is
Jordan multiplication by the Gram sum. Its quadratic trace is a sum of two
Gram traces, with an exact joint-kernel criterion. These results do not need
square-zero; that additional hypothesis is used only for the differential laws.
No new inner-product instance, norm, or mathematical definition is introduced.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceGradedTraceGeometry

open Matrix InfoGeometry.Core.IdempotentCartan PeirceGradedDifferential
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p : Matrix n n ℂ}

/-- Reflection is self-adjoint for the bilinear trace pairing. -/
theorem trace_reflection_conj_mul (hp : IsIdempotentElem p) (X Y : Matrix n n ℂ) :
    trace (reflectionConj p hp.eq X * Y) = trace (X * reflectionConj p hp.eq Y) := by
  change trace ((reflection p * X * reflection p) * Y) =
    trace (X * (reflection p * Y * reflection p))
  calc
    _ = trace (reflection p * (X * (reflection p * Y))) := by simp only [mul_assoc]
    _ = trace ((X * (reflection p * Y)) * reflection p) := trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

/-- The Hilbert--Schmidt adjoint has a plus sign, with actual oddness required. -/
theorem trace_star_twisted_minus (hp : IsStarProjection p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.isIdempotentElem.eq U = -U) (X Y : Matrix n n ℂ) :
    trace (star (U * X - reflectionConj p hp.isIdempotentElem.eq X * U) * Y) =
      trace (star X * (star U * Y + reflectionConj p hp.isIdempotentElem.eq Y * star U)) := by
  calc
    _ = trace (star X * (star U * Y)) -
        trace (star U * (reflectionConj p hp.isIdempotentElem.eq (star X) * Y)) := by
      simp only [star_sub, star_mul, ← reflection_conj_star hp, sub_mul, trace_sub, mul_assoc]
    _ = trace (star X * (star U * Y)) -
        trace (reflectionConj p hp.isIdempotentElem.eq (star X) * (Y * star U)) := by
      rw [trace_mul_comm (star U) (reflectionConj p hp.isIdempotentElem.eq (star X) * Y)]
      simp only [mul_assoc]
    _ = trace (star X * (star U * Y)) -
        trace (star X * reflectionConj p hp.isIdempotentElem.eq (Y * star U)) := by
      rw [trace_reflection_conj_mul hp.isIdempotentElem]
    _ = trace (star X * (star U * Y)) +
        trace (star X * (reflectionConj p hp.isIdempotentElem.eq Y * star U)) := by
      rw [map_mul, star_is_odd hp hU, mul_neg, mul_neg, trace_neg, sub_neg_eq_add]
    _ = _ := by rw [mul_add, trace_add]

/-- The reverse trace-adjoint identity follows by conjugating the pairing. -/
theorem trace_star_twisted_plus (hp : IsStarProjection p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.isIdempotentElem.eq U = -U) (X Y : Matrix n n ℂ) :
    trace (star (star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U) * Y) =
      trace (star X * (U * Y - reflectionConj p hp.isIdempotentElem.eq Y * U)) := by
  have h := congrArg star (trace_star_twisted_minus hp hU Y X)
  rw [← trace_conjTranspose, ← trace_conjTranspose] at h
  simpa only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose] using h.symm

/-- The quadratic trace of the Jordan action is the sum of two squared trace norms. -/
theorem trace_graded_laplacian (hp : IsStarProjection p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.isIdempotentElem.eq U = -U) (X : Matrix n n ℂ) :
    trace (star X * ((U * star U + star U * U) * X + X * (U * star U + star U * U))) =
      trace (star (U * X - reflectionConj p hp.isIdempotentElem.eq X * U) *
        (U * X - reflectionConj p hp.isIdempotentElem.eq X * U)) +
      trace (star (star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U) *
        (star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U)) := by
  rw [← twisted_minus_plus_anticommutator hp.isIdempotentElem hU (star_is_odd hp hU),
    mul_add, trace_add,
    ← trace_star_twisted_plus hp hU X,
    ← trace_star_twisted_minus hp hU X]
  exact add_comm _ _

/-- Positivity is for the Hilbert--Schmidt quadratic form on the full matrix space. -/
theorem trace_graded_laplacian_nonneg (hp : IsStarProjection p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.isIdempotentElem.eq U = -U) (X : Matrix n n ℂ) :
    0 ≤ trace (star X * ((U * star U + star U * U) * X + X * (U * star U + star U * U))) := by
  rw [trace_graded_laplacian hp hU]
  exact add_nonneg (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
    (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg

/-- Vanishing of the quadratic form detects both graded actions faithfully. -/
theorem trace_graded_laplacian_eq_zero_iff (hp : IsStarProjection p)
    {U : Matrix n n ℂ} (hU : reflectionConj p hp.isIdempotentElem.eq U = -U)
    (X : Matrix n n ℂ) :
    trace (star X * ((U * star U + star U * U) * X + X * (U * star U + star U * U))) = 0 ↔
      U * X - reflectionConj p hp.isIdempotentElem.eq X * U = 0 ∧
        star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U = 0 := by
  rw [trace_graded_laplacian hp hU,
    add_eq_zero_iff_of_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg]
  change (trace ((U * X - reflectionConj p hp.isIdempotentElem.eq X * U)ᴴ *
      (U * X - reflectionConj p hp.isIdempotentElem.eq X * U)) = 0 ∧
    trace ((star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U)ᴴ *
      (star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U)) = 0) ↔ _
  rw [trace_conjTranspose_mul_self_eq_zero_iff, trace_conjTranspose_mul_self_eq_zero_iff]

/-- The Jordan operator kernel is exactly the joint kernel of the adjoint pair. -/
theorem graded_laplacian_kernel (hp : IsStarProjection p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.isIdempotentElem.eq U = -U) (X : Matrix n n ℂ) :
    (U * star U + star U * U) * X + X * (U * star U + star U * U) = 0 ↔
      U * X - reflectionConj p hp.isIdempotentElem.eq X * U = 0 ∧
        star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U = 0 := by
  constructor
  · intro h
    apply (trace_graded_laplacian_eq_zero_iff hp hU X).mp
    rw [h, mul_zero, trace_zero]
  · rintro ⟨hd, hδ⟩
    rw [← twisted_minus_plus_anticommutator hp.isIdempotentElem hU (star_is_odd hp hU)]
    simp only [hd, hδ, map_zero, mul_zero, zero_mul, sub_self, add_zero]

/-- Nilpotence is an additional hypothesis for the adjoint differential square. -/
theorem adjoint_twisted_plus_square_zero (hp : IsStarProjection p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.isIdempotentElem.eq U = -U) (hUU : U * U = 0)
    (X : Matrix n n ℂ) :
    star U * (star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U) +
      reflectionConj p hp.isIdempotentElem.eq
        (star U * X + reflectionConj p hp.isIdempotentElem.eq X * star U) * star U = 0 := by
  have hs : star U * star U = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hUU
  rw [twisted_plus_square hp.isIdempotentElem (star_is_odd hp hU), hs, zero_lie]

end InfoGeometry.OperatorAlgebra.PeirceGradedTraceGeometry
