/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.NativeCuntzO3TriSupersymmetry

noncomputable section

namespace InfoGeometry.Algebra.NativeCuntzO3LieAlgebraCasimir

open InfoGeometry.Algebra.NativeCuntzO3TriSupersymmetry
open InfoGeometry.Algebra.CuntzTensorQuotient

def invTwo : Carrier := algebraMap ℂ Carrier ((2 : ℂ)⁻¹)

def invSix : Carrier := algebraMap ℂ Carrier ((6 : ℂ)⁻¹)

def casimir2 : Carrier :=
  Q12 * Q21 + Q21 * Q12 +
  Q23 * Q32 + Q32 * Q23 +
  Q31 * Q13 + Q13 * Q31 +
  invTwo * (Lambda3 * Lambda3) +
  invSix * (Lambda8 * Lambda8)

theorem cuntz_off_diagonal_root_sum :
    Q12 * Q21 + Q21 * Q12 +
    Q23 * Q32 + Q32 * Q23 +
    Q31 * Q13 + Q13 * Q31 = 2 := by
  rw [q12_q21_product, q21_q12_product,
    q23_q32_product, q32_q23_product,
    q31_q13_product, q13_q31_product]
  have hP : rangeProjection 0 + rangeProjection 1 + rangeProjection 2 = 1 := by
    rw [← q12_q21_product, ← q23_q32_product, ← q31_q13_product]
    exact tri_susy_hamiltonian_completeness
  calc
    rangeProjection 0 + rangeProjection 1 +
        rangeProjection 1 + rangeProjection 2 +
        rangeProjection 2 + rangeProjection 0 =
      2 * (rangeProjection 0 + rangeProjection 1 + rangeProjection 2) := by
        noncomm_ring
    _ = 2 := by
      rw [hP]
      norm_num

theorem lambda3_squared_casimir :
    Lambda3 * Lambda3 = rangeProjection 0 + rangeProjection 1 :=
  lambda3_squared

theorem lambda8_squared_casimir :
    Lambda8 * Lambda8 = rangeProjection 0 + rangeProjection 1 +
      4 * rangeProjection 2 :=
  lambda8_squared

/-- In the native tensor-algebra quotient, the quadratic expression is the
embedded scalar `2 + 1/2 + 1/6`. -/
theorem casimir2_eq_scalar :
    casimir2 = 2 + invTwo + invSix := by
  have hfour : (4 : Carrier) = algebraMap ℂ Carrier (4 : ℂ) :=
    (map_natCast (algebraMap ℂ Carrier) 4).symm
  have hcoeff : invTwo + invSix = 4 * invSix := by
    change algebraMap ℂ Carrier ((2 : ℂ)⁻¹) +
        algebraMap ℂ Carrier ((6 : ℂ)⁻¹) =
      4 * algebraMap ℂ Carrier ((6 : ℂ)⁻¹)
    rw [hfour, ← map_mul, ← map_add]
    norm_num
  dsimp [casimir2]
  rw [cuntz_off_diagonal_root_sum,
    lambda3_squared_casimir, lambda8_squared_casimir]
  have hcomplete : rangeProjection 0 + rangeProjection 1 +
      rangeProjection 2 = 1 := by
    rw [← q12_q21_product, ← q23_q32_product, ← q31_q13_product]
    exact tri_susy_hamiltonian_completeness
  have hcentralTwo (x : Carrier) : invTwo * x = x * invTwo := by
    dsimp [invTwo]
    exact Algebra.commutes ((2 : ℂ)⁻¹) x
  have hcentralSix (x : Carrier) : invSix * x = x * invSix := by
    dsimp [invSix]
    exact Algebra.commutes ((6 : ℂ)⁻¹) x
  have hcentralFour : invSix * (4 : Carrier) =
      (4 : Carrier) * invSix := by
    rw [hfour]
    dsimp [invSix]
    exact Algebra.commutes ((6 : ℂ)⁻¹) (algebraMap ℂ Carrier (4 : ℂ))
  calc
    2 + invTwo * (rangeProjection 0 + rangeProjection 1) +
        invSix * (rangeProjection 0 + rangeProjection 1 +
          4 * rangeProjection 2) =
      2 + (invTwo + invSix) *
          (rangeProjection 0 + rangeProjection 1) +
          (4 * invSix) * rangeProjection 2 := by
          simp only [mul_add, add_mul]
          rw [show invSix * (4 * rangeProjection 2) =
              4 * (invSix * rangeProjection 2) by
                calc
                  invSix * (4 * rangeProjection 2) =
                      (invSix * 4) * rangeProjection 2 := by rw [mul_assoc]
                  _ = (4 * invSix) * rangeProjection 2 := by rw [hcentralFour]
                  _ = 4 * (invSix * rangeProjection 2) := by rw [mul_assoc]]
          noncomm_ring
    _ = 2 + (4 * invSix) *
          (rangeProjection 0 + rangeProjection 1 + rangeProjection 2) := by
            rw [hcoeff]
            noncomm_ring
    _ = 2 + 4 * invSix := by rw [hcomplete, mul_one]
    _ = 2 + invTwo + invSix := by rw [← hcoeff]; abel

/-- The native quotient Casimir is central in its entire carrier. -/
theorem casimir2_commutes (x : Carrier) :
    lieBracket casimir2 x = 0 := by
  rw [casimir2_eq_scalar]
  dsimp [lieBracket]
  have hcentralTwo : invTwo * x = x * invTwo := by
    dsimp [invTwo]
    exact Algebra.commutes ((2 : ℂ)⁻¹) x
  have hcentralSix : invSix * x = x * invSix := by
    dsimp [invSix]
    exact Algebra.commutes ((6 : ℂ)⁻¹) x
  simp only [add_mul, mul_add, hcentralTwo, hcentralSix]
  noncomm_ring

theorem p3_q12_ortho :
    rangeProjection 2 * Q12 = 0 ∧ Q12 * rangeProjection 2 = 0 := by
  constructor
  · dsimp [rangeProjection, Q12]
    have h : cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (2 : Fin 3)) *
        (cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3))) =
        cuntzS 3 (2 : Fin 3) *
          (star (cuntzS 3 (2 : Fin 3)) * cuntzS 3 (0 : Fin 3)) *
          star (cuntzS 3 (1 : Fin 3)) := by
      noncomm_ring
    simp only [star_cuntzS] at h ⊢
    rw [h, cuntz_orthogonality]
    simp
  · dsimp [Q12, rangeProjection]
    have h : cuntzS 3 (0 : Fin 3) * star (cuntzS 3 (1 : Fin 3)) *
        (cuntzS 3 (2 : Fin 3) * star (cuntzS 3 (2 : Fin 3))) =
        cuntzS 3 (0 : Fin 3) *
          (star (cuntzS 3 (1 : Fin 3)) * cuntzS 3 (2 : Fin 3)) *
          star (cuntzS 3 (2 : Fin 3)) := by
      noncomm_ring
    simp only [star_cuntzS] at h ⊢
    rw [h, cuntz_orthogonality]
    simp

theorem casimir2_commutes_q12 :
    lieBracket casimir2 Q12 = 0 := by
  dsimp [lieBracket, casimir2]
  have hP : rangeProjection 0 + rangeProjection 1 + rangeProjection 2 = 1 := by
    rw [← q12_q21_product, ← q23_q32_product, ← q31_q13_product]
    exact tri_susy_hamiltonian_completeness
  rw [cuntz_off_diagonal_root_sum,
    lambda3_squared_casimir, lambda8_squared_casimir]
  have hproj := p3_q12_ortho
  have h1 : (2 : Carrier) * Q12 - Q12 * 2 = 0 := by
    noncomm_ring
  have hcentralTwo (x : Carrier) : invTwo * x = x * invTwo := by
    dsimp [invTwo]
    exact Algebra.commutes ((2 : ℂ)⁻¹) x
  have hcentralSix (x : Carrier) : invSix * x = x * invSix := by
    dsimp [invSix]
    exact Algebra.commutes ((6 : ℂ)⁻¹) x
  have htwoLeft (a b : Carrier) : a * (invTwo * b) = invTwo * (a * b) := by
    calc
      a * (invTwo * b) = (a * invTwo) * b := by rw [mul_assoc]
      _ = (invTwo * a) * b := by rw [hcentralTwo]
      _ = invTwo * (a * b) := by rw [mul_assoc]
  have htwoRight (a b : Carrier) : a * (b * invTwo) = (a * b) * invTwo := by
    rw [← mul_assoc]
  have hsixLeft (a b : Carrier) : a * (invSix * b) = invSix * (a * b) := by
    calc
      a * (invSix * b) = (a * invSix) * b := by rw [mul_assoc]
      _ = (invSix * a) * b := by rw [hcentralSix]
      _ = invSix * (a * b) := by rw [mul_assoc]
  have hsixRight (a b : Carrier) : a * (b * invSix) = (a * b) * invSix := by
    rw [← mul_assoc]
  have h2 : (rangeProjection 0 + rangeProjection 1) * Q12 -
      Q12 * (rangeProjection 0 + rangeProjection 1) = 0 := by
    have hsum : rangeProjection 0 + rangeProjection 1 =
        1 - rangeProjection 2 := by
      calc
        rangeProjection 0 + rangeProjection 1 =
            (rangeProjection 0 + rangeProjection 1 + rangeProjection 2) -
              rangeProjection 2 := by noncomm_ring
        _ = 1 - rangeProjection 2 := by
          rw [hP]
    rw [hsum]
    rcases hproj with ⟨hleft, hright⟩
    calc
      (1 - rangeProjection 2) * Q12 - Q12 * (1 - rangeProjection 2) =
            Q12 - rangeProjection 2 * Q12 -
            (Q12 - Q12 * rangeProjection 2) := by
              simp only [sub_mul, mul_sub]
              noncomm_ring
      _ = Q12 - 0 - (Q12 - 0) := by rw [hleft, hright]
      _ = 0 := by noncomm_ring
  have h3 : (rangeProjection 0 + rangeProjection 1 +
      4 * rangeProjection 2) * Q12 -
      Q12 * (rangeProjection 0 + rangeProjection 1 +
        4 * rangeProjection 2) = 0 := by
    have hsum : rangeProjection 0 + rangeProjection 1 +
        4 * rangeProjection 2 = 1 + 3 * rangeProjection 2 := by
      calc
        rangeProjection 0 + rangeProjection 1 + 4 * rangeProjection 2 =
            (rangeProjection 0 + rangeProjection 1 + rangeProjection 2) +
              3 * rangeProjection 2 := by noncomm_ring
        _ = 1 + 3 * rangeProjection 2 := by
          rw [hP]
    rw [hsum]
    rcases hproj with ⟨hleft, hright⟩
    calc
      (1 + 3 * rangeProjection 2) * Q12 -
          Q12 * (1 + 3 * rangeProjection 2) =
          Q12 + 3 * (rangeProjection 2 * Q12) -
            (Q12 + 3 * (Q12 * rangeProjection 2)) := by noncomm_ring
      _ = Q12 + 3 * 0 - (Q12 + 3 * 0) := by rw [hleft, hright]
      _ = 0 := by noncomm_ring
  calc
    (2 + invTwo * (rangeProjection 0 + rangeProjection 1) +
        invSix *
          (rangeProjection 0 + rangeProjection 1 + 4 * rangeProjection 2)) * Q12 -
      Q12 * (2 + invTwo * (rangeProjection 0 + rangeProjection 1) +
        invSix *
          (rangeProjection 0 + rangeProjection 1 + 4 * rangeProjection 2)) =
      (2 * Q12 - Q12 * 2) +
        invTwo *
          ((rangeProjection 0 + rangeProjection 1) * Q12 -
            Q12 * (rangeProjection 0 + rangeProjection 1)) +
        invSix *
          ((rangeProjection 0 + rangeProjection 1 + 4 * rangeProjection 2) * Q12 -
            Q12 * (rangeProjection 0 + rangeProjection 1 + 4 * rangeProjection 2)) := by
          simp only [sub_mul, mul_sub, add_mul, mul_add,
            neg_mul, mul_neg, neg_one_zsmul, zsmul_eq_mul]
          simp only [htwoLeft, htwoRight, hsixLeft, hsixRight]
          noncomm_ring
    _ = 0 + invTwo * 0 + invSix * 0 := by
      rw [h1, h2, h3]
    _ = 0 := by noncomm_ring

end InfoGeometry.Algebra.NativeCuntzO3LieAlgebraCasimir
