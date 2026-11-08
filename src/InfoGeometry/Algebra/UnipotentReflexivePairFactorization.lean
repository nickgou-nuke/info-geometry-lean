/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-! Associative ring identities for square-zero reflexive pairs.
No exact-order, star, or geometric interpretation is asserted.
-/

namespace InfoGeometry.Algebra.UnipotentReflexivePairFactorization

variable {A : Type*} [Ring A] {d B : A}

/-- The triple factorization only needs square-zero d and its inner-inverse law. -/
theorem unipotent_triple_factorization (hd : d * d = 0) (hdBd : d * B * d = d) :
    (1 + d) * (1 - B) * (1 + d) = 1 - d * B - B * d + d - B := by
  calc
    (1 + d) * (1 - B) * (1 + d) =
        1 + d + d + d * d - B - d * B - B * d - d * B * d := by noncomm_ring
    _ = 1 - d * B - B * d + d - B := by rw [hd, hdBd]; abel

/-- Reversing the factors and their signs gives a right inverse of the triple. -/
theorem unipotent_triple_mul_inverse (hd : d * d = 0) (hB : B * B = 0) :
    ((1 + d) * (1 - B) * (1 + d)) *
      ((1 - d) * (1 + B) * (1 - d)) = 1 := by
  have hdInv : (1 + d) * (1 - d) = 1 := by noncomm_ring [hd]
  have hBInv : (1 - B) * (1 + B) = 1 := by noncomm_ring [hB]
  calc
    _ = (1 + d) * (1 - B) * ((1 + d) * (1 - d)) * (1 + B) * (1 - d) := by
      simp only [mul_assoc]
    _ = 1 := by rw [hdInv, mul_one, mul_assoc (1 + d) (1 - B), hBInv, mul_one, hdInv]

/-- The same explicit inverse is also a left inverse. -/
theorem unipotent_inverse_mul_triple (hd : d * d = 0) (hB : B * B = 0) :
    ((1 - d) * (1 + B) * (1 - d)) *
      ((1 + d) * (1 - B) * (1 + d)) = 1 := by
  have hdInv : (1 - d) * (1 + d) = 1 := by noncomm_ring [hd]
  have hBInv : (1 + B) * (1 - B) = 1 := by noncomm_ring [hB]
  calc
    _ = (1 - d) * (1 + B) * ((1 - d) * (1 + d)) * (1 - B) * (1 + d) := by
      simp only [mul_assoc]
    _ = 1 := by rw [hdInv, mul_one, mul_assoc (1 - d) (1 + B), hBInv, mul_one, hdInv]

/-- The active support is idempotent without any star assumptions. -/
theorem support_square (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    (d * B + B * d) * (d * B + B * d) = d * B + B * d := by
  calc
    _ = (d * B * d) * B + d * (B * B) * d +
        B * (d * d) * B + (B * d * B) * d := by noncomm_ring
    _ = _ := by rw [hd, hB, hdBd, hBdB]; simp

theorem support_mul_skew (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    (d * B + B * d) * (d - B) = d - B := by
  calc
    _ = d * B * d - d * (B * B) + B * (d * d) - B * d * B := by noncomm_ring
    _ = _ := by rw [hd, hB, hdBd, hBdB]; simp

theorem skew_mul_support (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    (d - B) * (d * B + B * d) = d - B := by
  calc
    _ = (d * d) * B + d * B * d - B * d * B - (B * B) * d := by noncomm_ring
    _ = _ := by rw [hd, hB, hdBd, hBdB]; simp

/-- The skew operator squares to minus its active support. -/
theorem skew_square (hd : d * d = 0) (hB : B * B = 0) :
    (d - B) * (d - B) = -(d * B + B * d) := by
  noncomm_ring [hd, hB]

/-- The ambient skew extension is identity on the complementary support. -/
theorem ambient_skew_square (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    (1 - d * B - B * d + d - B) * (1 - d * B - B * d + d - B) =
      1 - 2 * (d * B + B * d) := by
  let S := d * B + B * d
  let J := d - B
  have hS : S * S = S := support_square hd hB hdBd hBdB
  have hSJ : S * J = J := support_mul_skew hd hB hdBd hBdB
  have hJS : J * S = J := skew_mul_support hd hB hdBd hBdB
  have hJ : J * J = -S := skew_square hd hB
  have hform : 1 - d * B - B * d + d - B = 1 - S + J := by dsimp [S, J]; abel
  rw [hform]
  change (1 - S + J) * (1 - S + J) = 1 - 2 * S
  noncomm_ring [hS, hSJ, hJS, hJ]

/-- Fourth power one is an identity, not a claim of exact multiplicative order. -/
theorem ambient_skew_fourth (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    (1 - d * B - B * d + d - B) ^ 4 = 1 := by
  let W := 1 - d * B - B * d + d - B
  let S := d * B + B * d
  have hW : W * W = 1 - 2 * S := ambient_skew_square hd hB hdBd hBdB
  have hS : S * S = S := support_square hd hB hdBd hBdB
  change W ^ 4 = 1
  calc
    W ^ 4 = (W * W) * (W * W) := by noncomm_ring
    _ = (1 - 2 * S) * (1 - 2 * S) := by rw [hW]
    _ = 1 := by noncomm_ring [hS]

end InfoGeometry.Algebra.UnipotentReflexivePairFactorization
