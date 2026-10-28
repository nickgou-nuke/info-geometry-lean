/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.NonCommutativeFredholmIndex
import InfoGeometry.Clifford.LorentzianBivectorSignatureBridge
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Bilinear Clifford matrix products with exact commutation defects

These are identities in a full matrix ring. No connection, metric, time
parameter, elliptic operator, or geometric Lichnerowicz formula is defined.
The coefficient matrices need not commute with each other. The primary
identity also retains all failures of coefficient–Clifford commutation.
-/

namespace InfoGeometry.NCG.CliffordMatrixProducts

open NonCommutativeFredholmIndex

variable {n R : Type*} [Fintype n] [DecidableEq n] [Ring R]
variable {a b X Y : Matrix n n R}

/-- Exact bilinear expansion, including all four cross-commutation defects. -/
theorem product_with_defects (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b + b * a = 0) (X Y U V : Matrix n n R) :
    (a * X + b * Y) * (a * U + b * V) =
      X * U + Y * V + (a * b) * (X * V - Y * U) +
        (a * commutator X a * U + a * commutator X b * V +
         b * commutator Y a * U + b * commutator Y b * V) := by
  have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_right hab
  calc
    _ = (a * a) * (X * U) + (b * b) * (Y * V) +
        (a * b) * (X * V) + (b * a) * (Y * U) +
        (a * commutator X a * U + a * commutator X b * V +
         b * commutator Y a * U + b * commutator Y b * V) := by
      unfold NonCommutativeFredholmIndex.commutator
      noncomm_ring
    _ = _ := by rw [ha, hb, hba]; noncomm_ring

/-- Right coefficients U,V are arbitrary: only X,Y cross the generators. -/
theorem product_of_commute (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b + b * a = 0)
    (hXa : Commute X a) (hXb : Commute X b)
    (hYa : Commute Y a) (hYb : Commute Y b) (U V : Matrix n n R) :
    (a * X + b * Y) * (a * U + b * V) =
      X * U + Y * V + (a * b) * (X * V - Y * U) := by
  rw [product_with_defects ha hb hab]
  simp only [NonCommutativeFredholmIndex.commutator, hXa.eq, hXb.eq,
    hYa.eq, hYb.eq, sub_self, mul_zero, zero_mul, add_zero]

section Commutant

variable (ha : a * a = 1) (hb : b * b = 1) (hab : a * b + b * a = 0)
variable (hXa : Commute X a) (hXb : Commute X b)
variable (hYa : Commute Y a) (hYb : Commute Y b)

include ha hb hab hXa hXb hYa hYb

theorem sum_square :
    (a * X + b * Y) * (a * X + b * Y) =
      X * X + Y * Y + (a * b) * commutator X Y :=
  product_of_commute ha hb hab hXa hXb hYa hYb X Y

theorem difference_square :
    (a * X - b * Y) * (a * X - b * Y) =
      X * X + Y * Y - (a * b) * commutator X Y := by
  have h := product_of_commute ha hb hab hXa hXb hYa.neg_left hYb.neg_left X (-Y)
  unfold NonCommutativeFredholmIndex.commutator
  convert h using 1 <;> noncomm_ring

theorem sum_mul_difference :
    (a * X + b * Y) * (a * X - b * Y) =
      X * X - Y * Y - (a * b) * anticommutator X Y := by
  have h := product_of_commute ha hb hab hXa hXb hYa hYb X (-Y)
  unfold NonCommutativeFredholmIndex.anticommutator
  convert h using 1 <;> noncomm_ring

theorem difference_mul_sum :
    (a * X - b * Y) * (a * X + b * Y) =
      X * X - Y * Y + (a * b) * anticommutator X Y := by
  have h := product_of_commute ha hb hab hXa hXb hYa.neg_left hYb.neg_left X Y
  unfold NonCommutativeFredholmIndex.anticommutator
  convert h using 1 <;> noncomm_ring

theorem squares_add :
    (a * X + b * Y) * (a * X + b * Y) +
      (a * X - b * Y) * (a * X - b * Y) = 2 • (X * X + Y * Y) := by
  rw [sum_square ha hb hab hXa hXb hYa hYb,
    difference_square ha hb hab hXa hXb hYa hYb, two_nsmul]
  abel

theorem squares_sub :
    (a * X + b * Y) * (a * X + b * Y) -
      (a * X - b * Y) * (a * X - b * Y) =
        2 • ((a * b) * commutator X Y) := by
  rw [sum_square ha hb hab hXa hXb hYa hYb,
    difference_square ha hb hab hXa hXb hYa hYb, two_nsmul]
  abel

theorem cross_anticommutator :
    anticommutator (a * X + b * Y) (a * X - b * Y) =
      2 • (X * X - Y * Y) := by
  rw [NonCommutativeFredholmIndex.anticommutator,
    sum_mul_difference ha hb hab hXa hXb hYa hYb,
    difference_mul_sum ha hb hab hXa hXb hYa hYb, two_nsmul]
  abel

theorem cross_commutator :
    commutator (a * X + b * Y) (a * X - b * Y) =
      -(2 • ((a * b) * anticommutator X Y)) := by
  rw [NonCommutativeFredholmIndex.commutator,
    sum_mul_difference ha hb hab hXa hXb hYa hYb,
    difference_mul_sum ha hb hab hXa hXb hYa hYb, two_nsmul]
  abel

end Commutant

omit [DecidableEq n] in
theorem factor_reversal_defect (a b X Y : Matrix n n R) :
    (a * X + b * Y) - (X * a + Y * b) =
      commutator a X + commutator b Y := by
  unfold NonCommutativeFredholmIndex.commutator
  abel

omit [DecidableEq n] in
/-- Native `Commute` closure gives conservation of the commutator summand. -/
theorem commute_curvature_term {C : Matrix n n R}
    (hCa : Commute C a) (hCb : Commute C b)
    (hCX : Commute C X) (hCY : Commute C Y) :
    Commute C ((a * b) * commutator X Y) :=
  (hCa.mul_right hCb).mul_right
    ((hCX.mul_right hCY).sub_right (hCY.mul_right hCX))

theorem commute_sum_of_products {C : Matrix n n R}
    (hCa : Commute C a) (hCb : Commute C b)
    (hCX : Commute C X) (hCY : Commute C Y) :
    Commute C (a * X + b * Y) :=
  (hCa.mul_right hCX).add_right (hCb.mul_right hCY)

/-- The existing square-minus-one result supplies invertibility of the bivector. -/
theorem bivector_isUnit (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b + b * a = 0) : IsUnit (a * b) := by
  have hs := Clifford.LorentzianBivectorSignatureBridge.positive_bivector_sq_neg_one
    ha hb hab
  refine ⟨⟨a * b, -(a * b), ?_, ?_⟩, rfl⟩
  · rw [mul_neg, hs, neg_neg]
  · rw [neg_mul, hs, neg_neg]

theorem conjugation_flips_second (ha : a * a = 1)
    (hab : a * b + b * a = 0) : a * b * a = -b := by
  have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_right hab
  rw [mul_assoc, hba, mul_neg, ← mul_assoc, ha, one_mul]

omit [DecidableEq n] in
theorem bivector_star [StarRing R] (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : a * b + b * a = 0) : star (a * b) = -(a * b) := by
  rw [star_mul, ha.star_eq, hb.star_eq]
  exact eq_neg_of_add_eq_zero_right hab

end InfoGeometry.NCG.CliffordMatrixProducts
