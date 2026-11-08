/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.PeirceGrading
import InfoGeometry.NCG.NonCommutativeFredholmIndex
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Opposite-square Peirce pairs and their two nilpotent charges

Native Peirce grading on full matrix rings. The sum of the commutator and
odd part is square-zero; its paired anticommutator need not vanish.
These identities do not assert a physical BdG or analytic SUSY model.
-/

namespace InfoGeometry.NCG.PeirceOddPair

open NonCommutativeFredholmIndex Core.PeirceGrading

variable {n R : Type*} [Fintype n] [DecidableEq n] [Ring R]
variable {P : Matrix n n R}

theorem odd_add_commutator (P A : Matrix n n R) :
    odd P A + commutator P A = 2 • (P * A * (1 - P)) := by
  rw [odd_apply, NonCommutativeFredholmIndex.commutator, two_nsmul]
  noncomm_ring

theorem odd_sub_commutator (P A : Matrix n n R) :
    odd P A - commutator P A = 2 • ((1 - P) * A * P) := by
  rw [odd_apply, NonCommutativeFredholmIndex.commutator, two_nsmul]
  noncomm_ring

theorem commutator_anticommutes_odd (hP : IsIdempotentElem P) (A : Matrix n n R) :
    anticommutator (commutator P A) (odd P A) = 0 := by
  have hγ := odd_anticommutes_reflection hP (commutator_odd hP A)
  have hr := (odd_reconstruction hP A).1
  change odd P A = reflection P * commutator P A at hr
  change reflection P * commutator P A + commutator P A * reflection P = 0 at hγ
  rw [hr]
  calc
    _ = (commutator P A * reflection P + reflection P * commutator P A) *
        commutator P A := by
      unfold NonCommutativeFredholmIndex.anticommutator
      noncomm_ring
    _ = 0 := by rw [add_comm, hγ, zero_mul]

theorem odd_add_commutator_sq_zero (hP : IsIdempotentElem P) (A : Matrix n n R) :
    (odd P A + commutator P A) * (odd P A + commutator P A) = 0 := by
  have h := (corners_sq_zero hP A).1
  rw [pow_two] at h
  rw [odd_add_commutator, two_nsmul]
  simp only [add_mul, mul_add, h, zero_add]

theorem odd_sub_commutator_sq_zero (hP : IsIdempotentElem P) (A : Matrix n n R) :
    (odd P A - commutator P A) * (odd P A - commutator P A) = 0 := by
  have h := (corners_sq_zero hP A).2
  rw [pow_two] at h
  rw [odd_sub_commutator, two_nsmul]
  simp only [add_mul, mul_add, h, zero_add]

theorem opposite_squares (hP : IsIdempotentElem P) (A : Matrix n n R) :
    commutator P A * commutator P A + odd P A * odd P A = 0 := by
  calc
    _ = (odd P A + commutator P A) * (odd P A + commutator P A) -
        anticommutator (commutator P A) (odd P A) := by
      unfold NonCommutativeFredholmIndex.anticommutator
      noncomm_ring
    _ = 0 := by rw [odd_add_commutator_sq_zero hP,
      commutator_anticommutes_odd hP, sub_self]

/-- The two square-zero charges have a possibly nonzero even anticommutator. -/
theorem charge_anticommutator (hP : IsIdempotentElem P) (A : Matrix n n R) :
    anticommutator (odd P A + commutator P A) (odd P A - commutator P A) =
      4 • (odd P A * odd P A) := by
  have hD : commutator P A * commutator P A = -(odd P A * odd P A) :=
    eq_neg_of_add_eq_zero_left (opposite_squares hP A)
  calc
    _ = 2 • (odd P A * odd P A) - 2 • (commutator P A * commutator P A) := by
      unfold NonCommutativeFredholmIndex.anticommutator
      simp only [two_nsmul]
      noncomm_ring
    _ = _ := by rw [hD]; abel

theorem reflection_anticommutes_charge (hP : IsIdempotentElem P) (A : Matrix n n R) :
    anticommutator (reflection P) (odd P A + commutator P A) = 0 := by
  have hM := odd_anticommutes_reflection hP
    (LinearMap.mem_range_self (odd P) A)
  have hD := odd_anticommutes_reflection hP (commutator_odd hP A)
  change reflection P * commutator P A + commutator P A * reflection P = 0 at hD
  calc
    _ = (reflection P * odd P A + odd P A * reflection P) +
        (reflection P * commutator P A + commutator P A * reflection P) := by
      unfold NonCommutativeFredholmIndex.anticommutator
      noncomm_ring
    _ = 0 := by rw [hM, hD, add_zero]

theorem reflection_commutes_odd_square (hP : IsIdempotentElem P) (A : Matrix n n R) :
    commutator (reflection P) (odd P A * odd P A) = 0 :=
  commutator_sq_of_anticomm_zero _ _
    (odd_anticommutes_reflection hP (LinearMap.mem_range_self (odd P) A))

theorem charge_commutes_odd_square (hP : IsIdempotentElem P) (A : Matrix n n R) :
    Commute (odd P A + commutator P A) (odd P A * odd P A) := by
  have h := commutator_sq_of_anticomm_zero _ _ (commutator_anticommutes_odd hP A)
  have hDM : commutator P A * (odd P A * odd P A) =
      (odd P A * odd P A) * commutator P A := sub_eq_zero.mp h
  change (odd P A + commutator P A) * (odd P A * odd P A) =
    (odd P A * odd P A) * (odd P A + commutator P A)
  simp only [add_mul, mul_add, hDM, mul_assoc]

section Star
variable [StarRing R]

omit [DecidableEq n] in
theorem commutator_star {A : Matrix n n R}
    (hP : IsSelfAdjoint P) (hA : IsSelfAdjoint A) :
    star (commutator P A) = -commutator P A := by
  simp only [NonCommutativeFredholmIndex.commutator, star_sub, star_mul,
    hP.star_eq, hA.star_eq]
  abel

theorem odd_star {A : Matrix n n R}
    (hP : IsSelfAdjoint P) (hA : IsSelfAdjoint A) : star (odd P A) = odd P A := by
  simp only [odd_apply, star_add, star_mul, star_sub, star_one, hP.star_eq, hA.star_eq]
  noncomm_ring

theorem charges_are_adjoints {A : Matrix n n R}
    (hP : IsSelfAdjoint P) (hA : IsSelfAdjoint A) :
    star (odd P A + commutator P A) = odd P A - commutator P A := by
  rw [star_add, odd_star hP hA, commutator_star hP hA, sub_eq_add_neg]

end Star

end InfoGeometry.NCG.PeirceOddPair
