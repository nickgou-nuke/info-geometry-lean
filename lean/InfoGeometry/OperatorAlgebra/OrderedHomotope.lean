/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-! # Ordered associative homotopes

The fixed-kernel product is `X * T * Y` on the full associative ring. Its
Jordan associator is a nested skew product; symmetrization alone does not
retain the ordered product. Rational scalar multiplication supplies the
central half without imposing commutativity on the operator carrier.
-/

namespace InfoGeometry.OperatorAlgebra.OrderedHomotope

variable {A : Type*} [Ring A]

/-- The associative product with a fixed middle operator. -/
def product (T X Y : A) : A := X * T * Y

theorem product_assoc (T X Y Z : A) :
    product T (product T X Y) Z = product T X (product T Y Z) := by
  simp only [product, mul_assoc]

theorem product_add_left (T X Y Z : A) :
    product T (X + Y) Z = product T X Z + product T Y Z := by
  simp [product, add_mul]

theorem product_add_right (T X Y Z : A) :
    product T X (Y + Z) = product T X Y + product T X Z := by
  simp [product, mul_add]

theorem map_product {B : Type*} [Ring B] (f : A →+* B) (T X Y : A) :
    f (product T X Y) = product (f T) (f X) (f Y) := by
  simp [product]

variable [Algebra ℚ A]

/-- Symmetric part of the ordered product. -/
def jordan (T X Y : A) : A :=
  (1 / 2 : ℚ) • (product T X Y + product T Y X)

/-- Normalized antisymmetric part of the ordered product. -/
def bracket (T X Y : A) : A :=
  (1 / 2 : ℚ) • (product T X Y - product T Y X)

theorem jordan_comm (T X Y : A) : jordan T X Y = jordan T Y X := by
  simp only [jordan, add_comm]

theorem bracket_skew (T X Y : A) : bracket T X Y = -bracket T Y X := by
  simp only [bracket, smul_sub]
  module

@[simp] theorem bracket_self (T X : A) : bracket T X X = 0 := by
  simp [bracket]

@[simp] theorem jordan_self (T X : A) : jordan T X X = product T X X := by
  simp only [jordan, smul_add]
  module

theorem jordan_add_bracket (T X Y : A) :
    jordan T X Y + bracket T X Y = product T X Y := by
  simp only [jordan, bracket, smul_add, smul_sub]
  module

theorem product_sub_jordan (T X Y : A) :
    product T X Y - jordan T X Y = bracket T X Y := by
  rw [← jordan_add_bracket T X Y]
  abel

theorem bracket_eq_zero_iff (T X Y : A) :
    bracket T X Y = 0 ↔ product T X Y = product T Y X := by
  simp [bracket, smul_eq_zero, sub_eq_zero]

theorem bracket_ne_zero_iff (T X Y : A) :
    bracket T X Y ≠ 0 ↔ product T X Y ≠ product T Y X :=
  not_congr (bracket_eq_zero_iff T X Y)

/-- Exact noncommutative obstruction to Jordan associativity. -/
theorem jordan_associator (T X Y Z : A) :
    jordan T (jordan T X Y) Z - jordan T X (jordan T Y Z) =
      bracket T Y (bracket T X Z) := by
  simp only [jordan, bracket, product, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, mul_assoc]
  module

/-- The skew part satisfies Jacobi for every fixed kernel. -/
theorem bracket_jacobi (T X Y Z : A) :
    bracket T X (bracket T Y Z) + bracket T Y (bracket T Z X) +
      bracket T Z (bracket T X Y) = 0 := by
  simp only [bracket, product, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, smul_sub, smul_smul, mul_assoc]
  module

/-- The symmetric part satisfies the Jordan identity on the same carrier. -/
theorem jordan_identity (T X Y : A) :
    jordan T (jordan T (jordan T X X) Y) X =
      jordan T (jordan T X X) (jordan T Y X) := by
  apply sub_eq_zero.mp
  rw [jordan_associator]
  have h : bracket T (jordan T X X) X = 0 := by
    rw [jordan_self, bracket_eq_zero_iff]
    exact product_assoc T X X X
  rw [h]
  simp [bracket, product]

end InfoGeometry.OperatorAlgebra.OrderedHomotope
