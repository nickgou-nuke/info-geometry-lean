/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Associative homotopes and the exact loss under symmetrization

A fixed kernel `T` changes the product of an associative ring to `x * T * y`.
The coefficient ring used for taking halves is commutative, but the operator
carrier is an arbitrary ring. No pairwise commutativity is assumed.

The generic ordered product and its commutator are distinct from the
Peirce-supported `upperHomotopeBracket` in `PeirceSpine/KantorCornerAnomaly`.
This file does not infer chronological irreversibility from a nonzero bracket.
-/

namespace InfoGeometry.Algebra.AssociativeHomotope

variable {A : Type*} [Ring A]

/-- Associative multiplication through a fixed kernel. -/
def product (T x y : A) : A := x * T * y

/-- The unnormalized commutator for the fixed-kernel product. -/
def bracket (T x y : A) : A := product T x y - product T y x

theorem product_assoc (T x y z : A) :
    product T (product T x y) z = product T x (product T y z) := by
  simp only [product, mul_assoc]

theorem product_add_left (T x y z : A) :
    product T (x + y) z = product T x z + product T y z := by
  simp only [product, add_mul]

theorem product_add_right (T x y z : A) :
    product T x (y + z) = product T x y + product T x z := by
  simp only [product, mul_add]

/-- For a unit kernel the new multiplicative identity is its inverse. -/
theorem product_inv_kernel_left (T : Aˣ) (x : A) :
    product (T : A) (↑T⁻¹ : A) x = x := by
  simp [product]

theorem product_inv_kernel_right (T : Aˣ) (x : A) :
    product (T : A) x (↑T⁻¹ : A) = x := by
  simp [product, mul_assoc]

/-- Ring maps transport the kernel as well as the two ordered inputs. -/
theorem map_product {B : Type*} [Ring B] (f : A →+* B) (T x y : A) :
    f (product T x y) = product (f T) (f x) (f y) := by
  simp [product]

/-- Multiplication by the kernel intertwines homotope and original products. -/
theorem kernel_mul_product (T x y : A) :
    T * product T x y = (T * x) * (T * y) := by
  simp only [product, mul_assoc]

@[simp] theorem bracket_self (T x : A) : bracket T x x = 0 := by
  simp [bracket]

theorem bracket_swap (T x y : A) : bracket T x y = -bracket T y x := by
  simp [bracket]

/-- The Jacobi law uses associativity and keeps every multiplication ordered. -/
theorem bracket_jacobi (T x y z : A) :
    bracket T x (bracket T y z) + bracket T y (bracket T z x) +
      bracket T z (bracket T x y) = 0 := by
  simp only [bracket, product]
  noncomm_ring

/-- Commuting with `x` is a derivation for the homotope multiplication. -/
theorem bracket_product (T x y z : A) :
    bracket T x (product T y z) =
      product T (bracket T x y) z + product T y (bracket T x z) := by
  simp only [bracket, product]
  noncomm_ring

section Halves

variable (R : Type*) [CommRing R] [Invertible (2 : R)] [Module R A]

/-- The symmetrized homotope. -/
def jordan (T x y : A) : A := (⅟2 : R) • (product T x y + product T y x)

/-- The normalized skew part, with the same factor of one half. -/
def skew (T x y : A) : A := (⅟2 : R) • bracket T x y

/-- Symmetrization cannot by itself retain an antisymmetric component. -/
theorem jordan_swap (T x y : A) : jordan R T x y = jordan R T y x := by
  simp only [jordan, add_comm]

theorem skew_swap (T x y : A) : skew R T x y = -skew R T y x := by
  rw [skew, bracket_swap, smul_neg]
  rfl

/-- Exact reconstruction of the ordered product from the two parts. -/
theorem jordan_add_skew (T x y : A) :
    jordan R T x y + skew R T x y = product T x y := by
  unfold jordan skew bracket
  rw [← smul_add]
  have h : (product T x y + product T y x) +
      (product T x y - product T y x) = product T x y + product T x y := by
    abel
  rw [h, smul_add, invOf_two_smul_add_invOf_two_smul R]

/-- The exact discarded term under symmetrization is the normalized bracket. -/
theorem product_sub_jordan (T x y : A) :
    product T x y - jordan R T x y = skew R T x y := by
  rw [← jordan_add_skew R T x y]
  abel

/-- The skew part vanishes precisely when this pair of ordered products agrees. -/
theorem skew_eq_zero_iff (T x y : A) :
    skew R T x y = 0 ↔ product T x y = product T y x := by
  constructor
  · intro h
    have h' := congrArg (fun v : A => (2 : R) • v) h
    simp only [skew, smul_smul, mul_invOf_self, one_smul, smul_zero] at h'
    exact sub_eq_zero.mp h'
  · intro h
    simp [skew, bracket, h]

/-- Equality with the symmetrization is equivalent to absence of order dependence. -/
theorem product_eq_jordan_iff (T x y : A) :
    product T x y = jordan R T x y ↔ product T x y = product T y x := by
  rw [← sub_eq_zero, product_sub_jordan, skew_eq_zero_iff]

end Halves

end InfoGeometry.Algebra.AssociativeHomotope
