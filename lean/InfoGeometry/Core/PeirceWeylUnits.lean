/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DiracSuperalgebra

/-!
# Weyl units and supported cyclotomic operators of a square-zero MP pair

This file reuses the existing support and Majorana owners. The new ambient
Weyl element is the skew Majorana generator completed by the harmonic
identity. Polynomial constant terms in the active corner are `activeSupport`,
not the ambient `1`. No exact order, principal bundle, connection, or Kähler
structure is inferred from these algebraic identities.
-/

namespace InfoGeometry.Core.PeirceWeylUnits

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

variable {A : Type*} [Ring A] [StarRing A]

/-- The supported root of `t² + t + 1`. -/
def thirdRoot (d b : A) : A := -coexactSupport d b + d - b

/-- The negative third root satisfies `t² - t + 1` in the active corner. -/
def sixthRoot (d b : A) : A := -thirdRoot d b

/-- Complete the skew generator by the identity on the harmonic complement. -/
def weylElement (d b : A) : A := harmonicSupport d b + majoranaMinus d b

/-- Its candidate inverse has the opposite skew part. -/
def weylInverse (d b : A) : A := harmonicSupport d b - majoranaMinus d b

variable {d b : A}

/-- The unipotent triple is already forced by square-zero and inner regularity. -/
theorem unipotent_triple (hd : d * d = 0) (hinner : d * b * d = d) :
    (1 + d) * (1 - b) * (1 + d) = weylElement d b := by
  unfold weylElement harmonicSupport exactSupport coexactSupport majoranaMinus
  calc
    (1 + d) * (1 - b) * (1 + d) =
        1 - d * b - b * d + d - b + d * d + (d - d * b * d) - b * (d * d) := by
      noncomm_ring
    _ = 1 - d * b - b * d + (d - b) := by rw [hd, hinner]; simp; abel

/-- The harmonic and skew parts annihilate in both orders. -/
theorem harmonic_skew_zero (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    harmonicSupport d b * majoranaMinus d b = 0 ∧
    majoranaMinus d b * harmonicSupport d b = 0 := by
  constructor
  · simp only [majoranaMinus, mul_sub, h.harmonicSupport_mul_eq_zero hd,
      h.harmonicSupport_mul_inverse_eq_zero hd, sub_self]
  · simp only [majoranaMinus, sub_mul, h.mul_harmonicSupport_eq_zero hd,
      h.inverse_mul_harmonicSupport_eq_zero hd, sub_self]

/-- The supported square is minus the active identity. -/
theorem skew_square (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    majoranaMinus d b * majoranaMinus d b = -activeSupport d b := by
  unfold majoranaMinus activeSupport exactSupport coexactSupport
  calc
    (d - b) * (d - b) = d * d - (d * b + b * d) + b * b := by noncomm_ring
    _ = -(d * b + b * d) := by rw [hd, h.inverse_sq_eq_zero hd]; abel

/-- Both inverse equations hold in the ambient ring, not merely the active corner. -/
theorem weyl_inverse_products (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    weylElement d b * weylInverse d b = 1 ∧
    weylInverse d b * weylElement d b = 1 := by
  rcases harmonic_skew_zero h hd with ⟨hl, hr⟩
  have h0 := h.harmonicSupport_idem hd
  have hj := skew_square h hd
  constructor <;>
    simp only [weylElement, weylInverse, add_mul, sub_mul, mul_add, mul_sub,
      h0, hl, hr, hj] <;>
    unfold harmonicSupport activeSupport <;> abel

/-- A genuine two-sided unit, including when the active support is proper. -/
def weylUnit (h : IsMoorePenroseInverse d b) (hd : d * d = 0) : Aˣ where
  val := weylElement d b
  inv := weylInverse d b
  val_inv := (weyl_inverse_products h hd).1
  inv_val := (weyl_inverse_products h hd).2

/-- The completed square is the sign change on the active summand. -/
theorem weyl_square (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    weylElement d b * weylElement d b = harmonicSupport d b - activeSupport d b := by
  rcases harmonic_skew_zero h hd with ⟨hl, hr⟩
  simp only [weylElement, add_mul, mul_add, h.harmonicSupport_idem hd,
    hl, hr, skew_square h hd, add_zero, zero_add, sub_eq_add_neg]

/-- The fourth power is one. This does not assert exact order four. -/
theorem weyl_fourth (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    weylElement d b ^ 4 = 1 := by
  have he := (activeSupport_identities h hd).1
  have hs := weyl_square h hd
  have hcomp : harmonicSupport d b = 1 - activeSupport d b := by
    unfold harmonicSupport activeSupport
    abel
  calc
    weylElement d b ^ 4 =
        (weylElement d b * weylElement d b) * (weylElement d b * weylElement d b) := by
      noncomm_ring
    _ = (1 - activeSupport d b - activeSupport d b) *
        (1 - activeSupport d b - activeSupport d b) := by rw [hs, hcomp]
    _ = 1 := by noncomm_ring [he]

/-- Ambient Weyl conjugation swaps the supports and reverses the arrows. -/
theorem weyl_conjugation (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    weylElement d b * exactSupport d b * weylInverse d b = coexactSupport d b ∧
    weylElement d b * coexactSupport d b * weylInverse d b = exactSupport d b ∧
    weylElement d b * d * weylInverse d b = -b ∧
    weylElement d b * b * weylInverse d b = -d := by
  rcases partial_matrix_unit_identities h hd with ⟨⟨hpd, hdq, hdp, hqd⟩,
    ⟨hqb, hbp, hbq, hpb⟩, _⟩
  have wp : weylElement d b * exactSupport d b = -b := by
    simp only [weylElement, majoranaMinus, add_mul, sub_mul,
      h.harmonicSupport_mul_exactSupport hd, hdp, hbp, zero_sub, zero_add]
  have wq : weylElement d b * coexactSupport d b = d := by
    simp only [weylElement, majoranaMinus, add_mul, sub_mul,
      h.harmonicSupport_mul_coexactSupport hd, hdq, hbq, sub_zero, zero_add]
  have bw : b * weylInverse d b = -coexactSupport d b := by
    simp only [weylInverse, majoranaMinus, mul_sub,
      h.inverse_mul_harmonicSupport_eq_zero hd, h.inverse_sq_eq_zero hd, sub_zero]
    rfl
  have dw : d * weylInverse d b = exactSupport d b := by
    simp only [weylInverse, majoranaMinus, mul_sub,
      h.mul_harmonicSupport_eq_zero hd, hd, zero_sub, neg_neg]
    rfl
  have wd : weylElement d b * d = -coexactSupport d b := by
    simp only [weylElement, majoranaMinus, add_mul, sub_mul,
      h.harmonicSupport_mul_eq_zero hd, hd, zero_sub, zero_add]
    rfl
  have wb : weylElement d b * b = exactSupport d b := by
    simp only [weylElement, majoranaMinus, add_mul, sub_mul,
      h.harmonicSupport_mul_inverse_eq_zero hd, h.inverse_sq_eq_zero hd, sub_zero, zero_add]
    rfl
  have qw : coexactSupport d b * weylInverse d b = b := by
    simp only [weylInverse, majoranaMinus, mul_sub,
      h.coexactSupport_mul_harmonicSupport hd, hqd, hqb, zero_sub, neg_neg]
  have pw : exactSupport d b * weylInverse d b = -d := by
    simp only [weylInverse, majoranaMinus, mul_sub,
      h.exactSupport_mul_harmonicSupport hd, hpd, hpb, sub_zero, zero_sub]
  exact ⟨by rw [wp, neg_mul, bw, neg_neg], by rw [wq, dw],
    by rw [wd, neg_mul, qw], by rw [wb, pw]⟩

/-- The supported third root has an explicit quadratic reduction. -/
theorem thirdRoot_square (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    thirdRoot d b * thirdRoot d b = -exactSupport d b - d + b := by
  rcases partial_matrix_unit_identities h hd with ⟨⟨_, hdq, _, hqd⟩,
    ⟨hqb, _, hbq, _⟩, _⟩
  unfold thirdRoot
  calc
    (-coexactSupport d b + d - b) * (-coexactSupport d b + d - b) =
      coexactSupport d b * coexactSupport d b - coexactSupport d b * d +
      coexactSupport d b * b - d * coexactSupport d b + d * d - d * b +
      b * coexactSupport d b - b * d + b * b := by noncomm_ring
    _ = -exactSupport d b - d + b := by
      rw [h.coexactSupport_idem, hqd, hqb, hdq, hd, hbq, h.inverse_sq_eq_zero hd]
      unfold exactSupport coexactSupport
      abel

/-- Actual cyclotomic-three relation, with the active identity as constant. -/
theorem thirdRoot_polynomial (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    thirdRoot d b * thirdRoot d b + thirdRoot d b + activeSupport d b = 0 := by
  rw [thirdRoot_square h hd]
  unfold thirdRoot activeSupport
  abel

/-- The third power is the active identity, not generally the ambient identity. -/
theorem thirdRoot_cube (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    thirdRoot d b ^ 3 = activeSupport d b := by
  rcases partial_matrix_unit_identities h hd with ⟨⟨hpd, hdq, _, _⟩,
    ⟨_, _, hbq, hpb⟩, _⟩
  rw [pow_succ, pow_two, thirdRoot_square h hd]
  unfold thirdRoot
  calc
    (-exactSupport d b - d + b) * (-coexactSupport d b + d - b) =
      exactSupport d b * coexactSupport d b - exactSupport d b * d +
      exactSupport d b * b + d * coexactSupport d b - d * d + d * b -
      b * coexactSupport d b + b * d - b * b := by noncomm_ring
    _ = activeSupport d b := by
      rw [h.exactSupport_mul_coexactSupport hd, hpd, hpb, hdq, hd, hbq,
        h.inverse_sq_eq_zero hd]
      unfold activeSupport exactSupport coexactSupport
      abel

/-- The negative third root satisfies the sixth-root polynomial and power laws. -/
theorem sixthRoot_laws (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    sixthRoot d b * sixthRoot d b - sixthRoot d b + activeSupport d b = 0 ∧
    sixthRoot d b ^ 3 = -activeSupport d b ∧
    sixthRoot d b ^ 6 = activeSupport d b := by
  have hc := thirdRoot_cube h hd
  have he := (activeSupport_identities h hd).1
  refine ⟨?_, ?_, ?_⟩
  · simpa [sixthRoot] using thirdRoot_polynomial h hd
  · simpa [sixthRoot] using congrArg Neg.neg hc
  · calc
      sixthRoot d b ^ 6 = (sixthRoot d b ^ 3) * (sixthRoot d b ^ 3) := by
        rw [← pow_add]
      _ = (-activeSupport d b) * (-activeSupport d b) := by
        have hcube : sixthRoot d b ^ 3 = -activeSupport d b := by
          simpa [sixthRoot] using congrArg Neg.neg hc
        rw [hcube]
      _ = activeSupport d b := by simpa using he

/-- The two supported finite-order operators recover the forward transvection. -/
theorem cyclotomic_pair_recovers_transvection
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    -majoranaMinus d b * thirdRoot d b = activeSupport d b + d := by
  unfold majoranaMinus thirdRoot activeSupport exactSupport coexactSupport
  calc
    -(d - b) * (-(b * d) + d - b) =
        d * b * d - d * d + d * b - (b * b) * d + b * d - b * b := by noncomm_ring
    _ = d * b + b * d + d := by
      rw [hd, h.inverse_sq_eq_zero hd, h.aba_eq_a]
      simp
      abel

end InfoGeometry.Core.PeirceWeylUnits
