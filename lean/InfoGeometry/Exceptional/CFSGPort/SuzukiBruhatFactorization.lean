/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
module

import InfoGeometry.Algebra.FiniteMatrixNoncommutativity
public import InfoGeometry.Exceptional.CFSGPort.SuzukiOvoidKernel

/-!
# Suzuki matrix Bruhat factorization

Root-pinned Lean 4.34.1 port of the external Suzuki Weyl–root factorization.
It proves two-cell Bruhat coverage and characterizes the local point
stabilizer on the four-dimensional operator carrier. Uniqueness of cell
parameters and the family simplicity theorem remain separate obligations.
-/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Suzuki

open InfoGeometry.Exceptional.CFSGPort.Chevalley
open Matrix

variable {a : ℕ} {K : Type} [Field K]

/-- Coordinate expansion of the Suzuki root matrix. -/
theorem suzukiS_eq_explicit (x y X Y : K)
    (hX : x ^ 2 ^ (a + 1) = X) (hY : y ^ 2 ^ (a + 1) = Y) :
    suzukiS a x y = !![1, 0, 0, 0; x, 1, 0, 0; y, X, 1, 0;
      X * x ^ 2 + x * y + Y, X * x + y, x, 1] := by
  rw [suzukiS, suzukiN, pow_add x (2 ^ (a + 1)) 2,
    pow_succ x (2 ^ (a + 1)), hX, hY]

/-- Explicit antidiagonal form of the Suzuki Weyl matrix. -/
theorem suzukiW_eq : suzukiW K =
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW]

/-- Unit powers reduce modulo the multiplicative group order. -/
theorem units_zpow_add_mul_card [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : Kˣ) (n k : ℤ) :
    x ^ (n + k * (2 ^ (2 * a + 1) - 1)) = x ^ n := by
  have h1 : x ^ ((2 ^ (2 * a + 1) - 1 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  have hcast : ((2 ^ (2 * a + 1) - 1 : ℕ) : ℤ) =
      2 ^ (2 * a + 1) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  rw [_root_.zpow_add, mul_comm k, _root_.zpow_mul, ← hcast,
    h1, _root_.one_zpow, mul_one]

/-- Diagonal expression for the special Suzuki torus parameter. -/
theorem suzukiD_two_sub_theta [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ) :
    suzukiD a (t ^ (2 - 2 ^ (a + 1) : ℤ)) =
      !![(t : K), 0, 0, 0;
        0, (t : K) ^ 2 ^ (a + 1) * (t : K)⁻¹, 0, 0;
        0, 0, (t : K) * ((t : K) ^ 2 ^ (a + 1))⁻¹, 0;
        0, 0, 0, (t : K)⁻¹] := by
  have e1 : (t ^ (2 - 2 ^ (a + 1) : ℤ)) ^ (1 + (2 ^ a : ℤ)) = t := by
    rw [← _root_.zpow_mul, show (2 - 2 ^ (a + 1) : ℤ) * (1 + 2 ^ a) =
      1 + (-1) * (2 ^ (2 * a + 1) - 1) by ring,
      units_zpow_add_mul_card hK, zpow_one]
  have e2 : (t ^ (2 - 2 ^ (a + 1) : ℤ)) ^ (2 ^ a : ℤ) =
      t ^ 2 ^ (a + 1) * t⁻¹ := by
    rw [← _root_.zpow_mul, show (2 - 2 ^ (a + 1) : ℤ) * 2 ^ a =
      ((2 ^ (a + 1) : ℕ) : ℤ) - 1 + (-1) * (2 ^ (2 * a + 1) - 1)
        by push_cast; ring,
      units_zpow_add_mul_card hK, _root_.zpow_sub_one, zpow_natCast]
  have e3 : (t ^ (2 - 2 ^ (a + 1) : ℤ)) ^ (-(2 ^ a : ℤ)) =
      t * (t ^ 2 ^ (a + 1))⁻¹ := by
    rw [_root_.zpow_neg, e2, _root_.mul_inv_rev, inv_inv, mul_comm]
  have e4 : (t ^ (2 - 2 ^ (a + 1) : ℤ)) ^ (-1 - (2 ^ a : ℤ)) = t⁻¹ := by
    rw [show (-1 - (2 ^ a : ℤ)) = -(1 + 2 ^ a) by ring,
      _root_.zpow_neg, e1]
  rw [suzukiD, e1, e2, e3, e4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_inv_eq_inv_val]

/-- The Suzuki norm is nonzero away from the origin. -/
theorem suzuki_norm_nonzero [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    suzukiN a u v = 0 ↔ u = 0 ∧ v = 0 :=
  suzukiNorm_eq_zero_iff a hK u v


private theorem suzuki_frob_data [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) : (2 : K) = 0 ∧ (∀ x y : K, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1)) ∧ ∀ x : K, (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2 := suzukiFrobData a hK

theorem suzukiBruhat_entry_00 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    (1) = V * τ * s ^ 2 + v ^ 2 * τ * s * S + v ^ 2 * V * τ * s ^ 2 * S + u * v * U * τ * s * S +
      (2) * u * v * U * V * τ * s ^ 2 * S + u ^ 2 * U ^ 2 * V * τ * s ^ 2 * S + u ^ 2 * v ^ 2 * U *
      τ * s ^ 2 * S + (2) * u ^ 3 * v * U ^ 2 * τ * s ^ 2 * S + u ^ 4 * U ^ 3 * τ * s ^ 2 * S := by
  linear_combination ((-1) * T * S + (-1) * τ * T * s * S + v ^ 2 * τ * T * s * S ^ 2 + u * v * U *
      τ * T * s * S ^ 2) * hts + ((-1) + V * τ * s ^ 2 + v ^ 2 * τ * s * S + (-1) * v ^ 2 * τ ^ 2 *
      s ^ 2 * S + u * v * U * τ * s * S + (-1) * u * v * U * τ ^ 2 * s ^ 2 * S) * hTS + (τ * T * s ^
      2 * S + (-1) * v ^ 2 * τ * s ^ 2 * S + (-2) * v ^ 2 * V * s ^ 2 * S + u * v * T * s ^ 2 * S +
      (-1) * u * v * U * τ * s ^ 2 * S + (-3) * u * v * U * V * s ^ 2 * S + (-1) * u * v ^ 3 * s ^ 2
      * S + u ^ 2 * U * T * s ^ 2 * S + (-1) * u ^ 2 * U ^ 2 * V * s ^ 2 * S + (-3) * u ^ 2 * v ^ 2
      * U * s ^ 2 * S + (-3) * u ^ 3 * v * U ^ 2 * s ^ 2 * S + (-1) * u ^ 4 * U ^ 3 * s ^ 2 * S) *
      ht + (u * v * V * s ^ 2 * S + u ^ 2 * U * V * s ^ 2 * S + u ^ 2 * v ^ 2 * s ^ 2 * S + (2) * u
      ^ 3 * v * U * s ^ 2 * S + u ^ 4 * U ^ 2 * s ^ 2 * S) * hT + ((-1) * v ^ 2 * V ^ 2 * s ^ 2 * S
      + (-1) * u * v * U * V ^ 2 * s ^ 2 * S + (-1) * u * v ^ 3 * V * s ^ 2 * S + (-3) * u ^ 2 * v ^
      2 * U * V * s ^ 2 * S + (-2) * u ^ 3 * v * U ^ 2 * V * s ^ 2 * S + (-1) * u ^ 3 * v ^ 3 * U *
      s ^ 2 * S + (-2) * u ^ 4 * v ^ 2 * U ^ 2 * s ^ 2 * S + (-1) * u ^ 5 * v * U ^ 3 * s ^ 2 * S) *
      h2

theorem suzukiBruhat_entry_01 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    u = v * τ * S + v * V * τ * s * S + u * U * V * τ * s * S + u ^ 2 * v * U * τ * s * S + u ^ 3 *
      U ^ 2 * τ * s * S := by
  linear_combination (v * τ * T * S ^ 2 + (-1) * u * T * S) * hts + (v * τ * S + (-1) * v * τ ^ 2 *
      s * S + (-1) * u) * hTS + ((-1) * v * τ * s * S + (-2) * v * V * s * S + u * T * s * S + (-1)
      * u * U * V * s * S + (-1) * u * v ^ 2 * s * S + (-2) * u ^ 2 * v * U * s * S + (-1) * u ^ 3 *
      U ^ 2 * s * S) * ht + (u * V * s * S + u ^ 2 * v * s * S + u ^ 3 * U * s * S) * hT + ((-1) * v
      * V ^ 2 * s * S + (-1) * u * v ^ 2 * V * s * S + (-2) * u ^ 2 * v * U * V * s * S + (-1) * u ^
      3 * v ^ 2 * U * s * S + (-1) * u ^ 4 * v * U ^ 2 * s * S) * h2

theorem suzukiBruhat_entry_02 {R : Type*} [CommRing R] (u v U τ s : R)
    (hts : τ * s = 1) :
    v + u * U = v * τ * s + u * U * τ * s := by
  linear_combination ((-1) * v + (-1) * u * U) * hts

theorem suzukiBruhat_entry_03 {R : Type*} [CommRing R] (u v U V τ : R)
    (ht : τ = U * u ^ 2 + u * v + V) :
    V + u * v + u ^ 2 * U = τ := by
  linear_combination ((-1)) * ht

theorem suzukiBruhat_entry_10 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = v * T * s * S + v * V * τ * s ^ 3 + v ^ 3 * τ * s ^ 2 * S + v ^ 3 * V * τ * s ^ 3 * S + u *
      v ^ 2 * U * τ * s ^ 2 * S + (2) * u * v ^ 2 * U * V * τ * s ^ 3 * S + u ^ 2 * v * U ^ 2 * V *
      τ * s ^ 3 * S + u ^ 2 * v ^ 3 * U * τ * s ^ 3 * S + (2) * u ^ 3 * v ^ 2 * U ^ 2 * τ * s ^ 3 *
      S + u ^ 4 * v * U ^ 3 * τ * s ^ 3 * S := by
  linear_combination (v * T ^ 2 * s * S ^ 2 + v * τ * T ^ 2 * s ^ 2 * S ^ 2 + v ^ 3 * τ * T * s ^ 2
      * S ^ 2 + u * v ^ 2 * U * τ * T * s ^ 2 * S ^ 2) * hts + (v * T * s * S + (-1) * v * τ ^ 2 * T
      * s ^ 3 * S + v * V * τ * s ^ 3 + v ^ 3 * τ * s ^ 2 * S + (-1) * v ^ 3 * τ ^ 2 * s ^ 3 * S + u
      * v ^ 2 * U * τ * s ^ 2 * S + (-1) * u * v ^ 2 * U * τ ^ 2 * s ^ 3 * S) * hTS + ((-1) * v * τ
      * T * s ^ 3 * S + (-2) * v * V * T * s ^ 3 * S + (-1) * v ^ 3 * τ * s ^ 3 * S + (-2) * v ^ 3 *
      V * s ^ 3 * S + (-1) * u * v ^ 2 * T * s ^ 3 * S + (-1) * u * v ^ 2 * U * τ * s ^ 3 * S + (-3)
      * u * v ^ 2 * U * V * s ^ 3 * S + (-1) * u * v ^ 4 * s ^ 3 * S + (-1) * u ^ 2 * v * U * T * s
      ^ 3 * S + (-1) * u ^ 2 * v * U ^ 2 * V * s ^ 3 * S + (-3) * u ^ 2 * v ^ 3 * U * s ^ 3 * S +
      (-3) * u ^ 3 * v ^ 2 * U ^ 2 * s ^ 3 * S + (-1) * u ^ 4 * v * U ^ 3 * s ^ 3 * S) * ht + ((-2)
      * v * V ^ 2 * s ^ 3 * S + (-3) * u * v ^ 2 * V * s ^ 3 * S + (-3) * u ^ 2 * v * U * V * s ^ 3
      * S + (-1) * u ^ 2 * v ^ 3 * s ^ 3 * S + (-2) * u ^ 3 * v ^ 2 * U * s ^ 3 * S + (-1) * u ^ 4 *
      v * U ^ 2 * s ^ 3 * S) * hT + ((-1) * v * U * V ^ 3 * s ^ 3 * S + (-2) * v ^ 3 * V ^ 2 * s ^ 3
      * S + (-3) * u * v ^ 2 * U * V ^ 2 * s ^ 3 * S + (-3) * u * v ^ 4 * V * s ^ 3 * S + (-3) * u ^
      2 * v * U ^ 2 * V ^ 2 * s ^ 3 * S + (-6) * u ^ 2 * v ^ 3 * U * V * s ^ 3 * S + (-1) * u ^ 2 *
      v ^ 5 * s ^ 3 * S + (-6) * u ^ 3 * v ^ 2 * U ^ 2 * V * s ^ 3 * S + (-3) * u ^ 3 * v ^ 4 * U *
      s ^ 3 * S + (-3) * u ^ 4 * v * U ^ 3 * V * s ^ 3 * S + (-4) * u ^ 4 * v ^ 3 * U ^ 2 * s ^ 3 *
      S + (-3) * u ^ 5 * v ^ 2 * U ^ 3 * s ^ 3 * S + (-1) * u ^ 6 * v * U ^ 4 * s ^ 3 * S) * h2

theorem suzukiBruhat_entry_11 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    (1) = V * T * s * S + v ^ 2 * τ * s * S + v ^ 2 * V * τ * s ^ 2 * S + u * v * U * V * τ * s ^ 2
      * S + u ^ 2 * U * T * s * S + u ^ 2 * v ^ 2 * U * τ * s ^ 2 * S + u ^ 3 * v * U ^ 2 * τ * s ^
      2 * S := by
  linear_combination ((-1) * T * S + (-1) * τ * T * s * S + V * T ^ 2 * s * S ^ 2 + v ^ 2 * τ * T *
      s * S ^ 2 + u ^ 2 * U * T ^ 2 * s * S ^ 2) * hts + ((-1) + V * T * s * S + (-1) * V * τ * T *
      s ^ 2 * S + v ^ 2 * τ * s * S + (-1) * v ^ 2 * τ ^ 2 * s ^ 2 * S + u ^ 2 * U * T * s * S +
      (-1) * u ^ 2 * U * τ * T * s ^ 2 * S) * hTS + (τ * T * s ^ 2 * S + (-1) * v ^ 2 * τ * s ^ 2 *
      S + (-2) * v ^ 2 * V * s ^ 2 * S + u * v * T * s ^ 2 * S + (-1) * u * v * U * V * s ^ 2 * S +
      (-1) * u * v ^ 3 * s ^ 2 * S + (-2) * u ^ 2 * v ^ 2 * U * s ^ 2 * S + (-1) * u ^ 3 * v * U ^ 2
      * s ^ 2 * S) * ht + (u * v * V * s ^ 2 * S + u ^ 2 * v ^ 2 * s ^ 2 * S + u ^ 3 * v * U * s ^ 2
      * S) * hT + ((-1) * v ^ 2 * V ^ 2 * s ^ 2 * S + (-1) * u * v ^ 3 * V * s ^ 2 * S + (-2) * u ^
      2 * v ^ 2 * U * V * s ^ 2 * S + (-1) * u ^ 3 * v ^ 3 * U * s ^ 2 * S + (-1) * u ^ 4 * v ^ 2 *
      U ^ 2 * s ^ 2 * S) * h2

theorem suzukiBruhat_entry_12 {R : Type*} [CommRing R] (u v U V τ T s : R)
    (hts : τ * s = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U * V + v ^ 2) (h2
    : (2 : R) = 0) :
    U = T * s + v ^ 2 * τ * s ^ 2 + u * v * U * τ * s ^ 2 := by
  linear_combination (T * s + (-1) * U + (-1) * U * τ * s) * hts + ((-1) * T * s ^ 2 + U * τ * s ^ 2
      + U * V * s ^ 2 + (-1) * v ^ 2 * s ^ 2 + u ^ 2 * U ^ 2 * s ^ 2) * ht + ((-1) * V * s ^ 2 +
      (-1) * u * v * s ^ 2 + (-1) * u ^ 2 * U * s ^ 2) * hT + ((-1) * v ^ 2 * V * s ^ 2 + (-1) * u *
      v ^ 3 * s ^ 2 + (-1) * u ^ 2 * v ^ 2 * U * s ^ 2) * h2

theorem suzukiBruhat_entry_13 {R : Type*} [CommRing R] (v τ s : R)
    (hts : τ * s = 1) :
    v = v * τ * s := by
  linear_combination ((-1) * v) * hts

theorem suzukiBruhat_entry_20 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = v * τ * s * S + v * V * T * s * S ^ 2 + u * V * τ * s ^ 3 + u * U * τ * s * S + u * v ^ 2 *
      τ * s ^ 2 * S + u * v ^ 2 * V * τ * s ^ 3 * S + u ^ 2 * v * U * τ * s ^ 2 * S + (2) * u ^ 2 *
      v * U * V * τ * s ^ 3 * S + u ^ 3 * U ^ 2 * V * τ * s ^ 3 * S + u ^ 3 * v ^ 2 * U * τ * s ^ 3
      * S + (2) * u ^ 4 * v * U ^ 2 * τ * s ^ 3 * S + u ^ 5 * U ^ 3 * τ * s ^ 3 * S := by
  linear_combination (v * τ * T ^ 2 * s * S ^ 3 + v * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 3 + v * V * T ^ 3
      * s * S ^ 4 + v * V * τ * T ^ 3 * s ^ 2 * S ^ 4 + u * U * τ * T ^ 2 * s * S ^ 3 + u * U * τ ^
      2 * T ^ 2 * s ^ 2 * S ^ 3 + u * v ^ 2 * τ * T ^ 2 * s ^ 2 * S ^ 3 + u ^ 2 * v * U * τ * T ^ 2
      * s ^ 2 * S ^ 3) * hts + (v * τ * s * S + v * τ * T * s * S ^ 2 + (-1) * v * τ ^ 3 * T * s ^ 3
      * S ^ 2 + v * V * T * s * S ^ 2 + v * V * T ^ 2 * s * S ^ 3 + (-1) * v * V * τ ^ 2 * T * s ^ 3
      * S ^ 2 + (-1) * v * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 3 + u * V * τ * s ^ 3 + u * V * τ * T * s
      ^ 3 * S + u * U * τ * s * S + u * U * τ * T * s * S ^ 2 + (-1) * u * U * τ ^ 3 * T * s ^ 3 * S
      ^ 2 + u * v ^ 2 * τ * s ^ 2 * S + u * v ^ 2 * τ * T * s ^ 2 * S ^ 2 + (-1) * u * v ^ 2 * τ ^ 2
      * T * s ^ 3 * S ^ 2 + u * v ^ 2 * V * τ * s ^ 3 * S + u ^ 2 * v * U * τ * s ^ 2 * S + u ^ 2 *
      v * U * τ * T * s ^ 2 * S ^ 2 + (-1) * u ^ 2 * v * U * τ ^ 2 * T * s ^ 3 * S ^ 2 + (2) * u ^ 2
      * v * U * V * τ * s ^ 3 * S + u ^ 3 * U ^ 2 * V * τ * s ^ 3 * S + u ^ 3 * v ^ 2 * U * τ * s ^
      3 * S + (2) * u ^ 4 * v * U ^ 2 * τ * s ^ 3 * S + u ^ 5 * U ^ 3 * τ * s ^ 3 * S) * hTS + ((-1)
      * v * τ ^ 2 * T * s ^ 3 * S ^ 2 + (-2) * v * V * τ * T * s ^ 3 * S ^ 2 + (-2) * v * V ^ 2 * T
      * s ^ 3 * S ^ 2 + (-1) * u * V * T ^ 2 * s ^ 3 * S ^ 2 + (-1) * u * U * τ ^ 2 * T * s ^ 3 * S
      ^ 2 + (-1) * u * U * V * τ * T * s ^ 3 * S ^ 2 + (-1) * u * U * V ^ 2 * T * s ^ 3 * S ^ 2 +
      (-2) * u * v ^ 2 * τ * T * s ^ 3 * S ^ 2 + (-5) * u * v ^ 2 * V * T * s ^ 3 * S ^ 2 + (-3) * u
      ^ 2 * v * U * τ * T * s ^ 3 * S ^ 2 + (-8) * u ^ 2 * v * U * V * T * s ^ 3 * S ^ 2 + (-2) * u
      ^ 2 * v ^ 3 * T * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * U ^ 2 * τ * T * s ^ 3 * S ^ 2 + (-3) * u ^ 3
      * U ^ 2 * V * T * s ^ 3 * S ^ 2 + (-6) * u ^ 3 * v ^ 2 * U * T * s ^ 3 * S ^ 2 + (-6) * u ^ 4
      * v * U ^ 2 * T * s ^ 3 * S ^ 2 + (-2) * u ^ 5 * U ^ 3 * T * s ^ 3 * S ^ 2) * ht + ((-2) * v *
      V ^ 3 * s ^ 3 * S ^ 2 + (-1) * u * V ^ 2 * T * s ^ 3 * S ^ 2 + (-2) * u * U * V ^ 3 * s ^ 3 *
      S ^ 2 + (-8) * u * v ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * V * T * s ^ 3 * S ^ 2 +
      (-12) * u ^ 2 * v * U * V ^ 2 * s ^ 3 * S ^ 2 + (-8) * u ^ 2 * v ^ 3 * V * s ^ 3 * S ^ 2 +
      (-1) * u ^ 3 * U * V * T * s ^ 3 * S ^ 2 + (-6) * u ^ 3 * U ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 +
      (-20) * u ^ 3 * v ^ 2 * U * V * s ^ 3 * S ^ 2 + (-2) * u ^ 3 * v ^ 4 * s ^ 3 * S ^ 2 + (-18) *
      u ^ 4 * v * U ^ 2 * V * s ^ 3 * S ^ 2 + (-8) * u ^ 4 * v ^ 3 * U * s ^ 3 * S ^ 2 + (-6) * u ^
      5 * U ^ 3 * V * s ^ 3 * S ^ 2 + (-12) * u ^ 5 * v ^ 2 * U ^ 2 * s ^ 3 * S ^ 2 + (-8) * u ^ 6 *
      v * U ^ 3 * s ^ 3 * S ^ 2 + (-2) * u ^ 7 * U ^ 4 * s ^ 3 * S ^ 2) * hT + ((-1) * v * U * V ^ 4
      * s ^ 3 * S ^ 2 + (-1) * v ^ 3 * V ^ 3 * s ^ 3 * S ^ 2 + (-1) * u * U ^ 2 * V ^ 4 * s ^ 3 * S
      ^ 2 + (-5) * u * v ^ 2 * U * V ^ 3 * s ^ 3 * S ^ 2 + (-4) * u * v ^ 4 * V ^ 2 * s ^ 3 * S ^ 2
      + (-7) * u ^ 2 * v * U ^ 2 * V ^ 3 * s ^ 3 * S ^ 2 + (-10) * u ^ 2 * v ^ 3 * U * V ^ 2 * s ^ 3
      * S ^ 2 + (-4) * u ^ 2 * v ^ 5 * V * s ^ 3 * S ^ 2 + (-4) * u ^ 3 * U ^ 3 * V ^ 3 * s ^ 3 * S
      ^ 2 + (-17) * u ^ 3 * v ^ 2 * U ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 + (-11) * u ^ 3 * v ^ 4 * U * V *
      s ^ 3 * S ^ 2 + (-1) * u ^ 3 * v ^ 6 * s ^ 3 * S ^ 2 + (-15) * u ^ 4 * v * U ^ 3 * V ^ 2 * s ^
      3 * S ^ 2 + (-17) * u ^ 4 * v ^ 3 * U ^ 2 * V * s ^ 3 * S ^ 2 + (-4) * u ^ 4 * v ^ 5 * U * s ^
      3 * S ^ 2 + (-6) * u ^ 5 * U ^ 4 * V ^ 2 * s ^ 3 * S ^ 2 + (-19) * u ^ 5 * v ^ 2 * U ^ 3 * V *
      s ^ 3 * S ^ 2 + (-7) * u ^ 5 * v ^ 4 * U ^ 2 * s ^ 3 * S ^ 2 + (-13) * u ^ 6 * v * U ^ 4 * V *
      s ^ 3 * S ^ 2 + (-8) * u ^ 6 * v ^ 3 * U ^ 3 * s ^ 3 * S ^ 2 + (-4) * u ^ 7 * U ^ 5 * V * s ^
      3 * S ^ 2 + (-7) * u ^ 7 * v ^ 2 * U ^ 4 * s ^ 3 * S ^ 2 + (-4) * u ^ 8 * v * U ^ 5 * s ^ 3 *
      S ^ 2 + (-1) * u ^ 9 * U ^ 6 * s ^ 3 * S ^ 2) * h2

theorem suzukiBruhat_entry_21 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = τ * S + V ^ 2 * T * s * S ^ 2 + u * v * τ * s * S + u * v * V * τ * s ^ 2 * S + u ^ 2 * U *
      V * T * s * S ^ 2 + u ^ 2 * U * V * τ * s ^ 2 * S + u ^ 3 * v * U * τ * s ^ 2 * S + u ^ 4 * U
      ^ 2 * τ * s ^ 2 * S := by
  linear_combination (τ * T ^ 2 * S ^ 3 + τ ^ 2 * T ^ 2 * s * S ^ 3 + V ^ 2 * T ^ 3 * s * S ^ 4 + u
      * v * τ * T ^ 2 * s * S ^ 3 + u ^ 2 * U * V * T ^ 3 * s * S ^ 4) * hts + (τ * S + τ * T * S ^
      2 + (-1) * τ ^ 3 * T * s ^ 2 * S ^ 2 + V ^ 2 * T * s * S ^ 2 + V ^ 2 * T ^ 2 * s * S ^ 3 +
      (-1) * V ^ 2 * τ * T * s ^ 2 * S ^ 2 + (-1) * V ^ 2 * τ * T ^ 2 * s ^ 2 * S ^ 3 + u * v * τ *
      s * S + u * v * τ * T * s * S ^ 2 + (-1) * u * v * τ ^ 2 * T * s ^ 2 * S ^ 2 + u * v * V * τ *
      s ^ 2 * S + u ^ 2 * U * V * T * s * S ^ 2 + u ^ 2 * U * V * T ^ 2 * s * S ^ 3 + u ^ 2 * U * V
      * τ * s ^ 2 * S + (-1) * u ^ 2 * U * V * τ * T * s ^ 2 * S ^ 2 + (-1) * u ^ 2 * U * V * τ * T
      ^ 2 * s ^ 2 * S ^ 3 + u ^ 3 * v * U * τ * s ^ 2 * S + u ^ 4 * U ^ 2 * τ * s ^ 2 * S) * hTS +
      ((-1) * τ ^ 2 * T * s ^ 2 * S ^ 2 + (-1) * V * τ * T * s ^ 2 * S ^ 2 + (-2) * V ^ 2 * T * s ^
      2 * S ^ 2 + (-2) * u * v * τ * T * s ^ 2 * S ^ 2 + (-4) * u * v * V * T * s ^ 2 * S ^ 2 + (-1)
      * u ^ 2 * U * τ * T * s ^ 2 * S ^ 2 + (-4) * u ^ 2 * U * V * T * s ^ 2 * S ^ 2 + (-2) * u ^ 2
      * v ^ 2 * T * s ^ 2 * S ^ 2 + (-4) * u ^ 3 * v * U * T * s ^ 2 * S ^ 2 + (-2) * u ^ 4 * U ^ 2
      * T * s ^ 2 * S ^ 2) * ht + ((-2) * V ^ 3 * s ^ 2 * S ^ 2 + (-6) * u * v * V ^ 2 * s ^ 2 * S ^
      2 + (-6) * u ^ 2 * U * V ^ 2 * s ^ 2 * S ^ 2 + (-6) * u ^ 2 * v ^ 2 * V * s ^ 2 * S ^ 2 +
      (-12) * u ^ 3 * v * U * V * s ^ 2 * S ^ 2 + (-2) * u ^ 3 * v ^ 3 * s ^ 2 * S ^ 2 + (-6) * u ^
      4 * U ^ 2 * V * s ^ 2 * S ^ 2 + (-6) * u ^ 4 * v ^ 2 * U * s ^ 2 * S ^ 2 + (-6) * u ^ 5 * v *
      U ^ 2 * s ^ 2 * S ^ 2 + (-2) * u ^ 6 * U ^ 3 * s ^ 2 * S ^ 2) * hT + ((-1) * U * V ^ 4 * s ^ 2
      * S ^ 2 + (-1) * v ^ 2 * V ^ 3 * s ^ 2 * S ^ 2 + (-3) * u * v * U * V ^ 3 * s ^ 2 * S ^ 2 +
      (-3) * u * v ^ 3 * V ^ 2 * s ^ 2 * S ^ 2 + (-4) * u ^ 2 * U ^ 2 * V ^ 3 * s ^ 2 * S ^ 2 + (-6)
      * u ^ 2 * v ^ 2 * U * V ^ 2 * s ^ 2 * S ^ 2 + (-3) * u ^ 2 * v ^ 4 * V * s ^ 2 * S ^ 2 + (-9)
      * u ^ 3 * v * U ^ 2 * V ^ 2 * s ^ 2 * S ^ 2 + (-7) * u ^ 3 * v ^ 3 * U * V * s ^ 2 * S ^ 2 +
      (-1) * u ^ 3 * v ^ 5 * s ^ 2 * S ^ 2 + (-6) * u ^ 4 * U ^ 3 * V ^ 2 * s ^ 2 * S ^ 2 + (-9) * u
      ^ 4 * v ^ 2 * U ^ 2 * V * s ^ 2 * S ^ 2 + (-3) * u ^ 4 * v ^ 4 * U * s ^ 2 * S ^ 2 + (-9) * u
      ^ 5 * v * U ^ 3 * V * s ^ 2 * S ^ 2 + (-4) * u ^ 5 * v ^ 3 * U ^ 2 * s ^ 2 * S ^ 2 + (-4) * u
      ^ 6 * U ^ 4 * V * s ^ 2 * S ^ 2 + (-4) * u ^ 6 * v ^ 2 * U ^ 3 * s ^ 2 * S ^ 2 + (-3) * u ^ 7
      * v * U ^ 4 * s ^ 2 * S ^ 2 + (-1) * u ^ 8 * U ^ 5 * s ^ 2 * S ^ 2) * h2

theorem suzukiBruhat_entry_22 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) :
    (1) = V * T * s * S + u * v * τ * s ^ 2 + u ^ 2 * U * τ * s ^ 2 := by
  linear_combination ((-1) * T * S + (-1) * τ * T * s * S + V * T ^ 2 * s * S ^ 2) * hts + ((-1) + V
      * T * s * S + (-1) * V * τ * T * s ^ 2 * S + u * v * τ * s ^ 2 + u ^ 2 * U * τ * s ^ 2) * hTS
      + (τ * T * s ^ 2 * S) * ht

theorem suzukiBruhat_entry_23 {R : Type*} [CommRing R] (u τ s : R)
    (hts : τ * s = 1) :
    u = u * τ * s := by
  linear_combination ((-1) * u) * hts

theorem suzukiBruhat_entry_30 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = s + U * V * τ * s ^ 2 * S + v ^ 2 * τ * s ^ 2 * S + v ^ 2 * V * T * s ^ 2 * S ^ 2 + v ^ 2 *
      V ^ 2 * τ * s ^ 4 * S + v ^ 2 * U * τ * s * S ^ 2 + v ^ 2 * U * V * τ * s ^ 2 * S ^ 2 + v ^ 4
      * V * τ * s ^ 3 * S ^ 2 + v ^ 4 * V ^ 2 * τ * s ^ 4 * S ^ 2 + u * v * T * s ^ 2 * S + u * v *
      V * τ * s ^ 4 + u * v * U * τ * s ^ 2 * S + u * v * U ^ 2 * τ * s * S ^ 2 + (2) * u * v * U ^
      2 * V * τ * s ^ 2 * S ^ 2 + u * v ^ 3 * τ * s ^ 3 * S + u * v ^ 3 * V * τ * s ^ 4 * S + u * v
      ^ 3 * U * V * τ * s ^ 3 * S ^ 2 + (2) * u * v ^ 3 * U * V ^ 2 * τ * s ^ 4 * S ^ 2 + u ^ 2 * U
      ^ 3 * V * τ * s ^ 2 * S ^ 2 + u ^ 2 * v ^ 2 * U * τ * s ^ 3 * S + (2) * u ^ 2 * v ^ 2 * U * V
      * τ * s ^ 4 * S + u ^ 2 * v ^ 2 * U ^ 2 * τ * s ^ 2 * S ^ 2 + u ^ 2 * v ^ 2 * U ^ 2 * V ^ 2 *
      τ * s ^ 4 * S ^ 2 + u ^ 2 * v ^ 4 * U * V * τ * s ^ 4 * S ^ 2 + u ^ 3 * v * U ^ 2 * V * τ * s
      ^ 4 * S + (2) * u ^ 3 * v * U ^ 3 * τ * s ^ 2 * S ^ 2 + u ^ 3 * v ^ 3 * U * τ * s ^ 4 * S +
      (2) * u ^ 3 * v ^ 3 * U ^ 2 * V * τ * s ^ 4 * S ^ 2 + u ^ 4 * U ^ 4 * τ * s ^ 2 * S ^ 2 + (2)
      * u ^ 4 * v ^ 2 * U ^ 2 * τ * s ^ 4 * S + u ^ 4 * v ^ 2 * U ^ 3 * V * τ * s ^ 4 * S ^ 2 + u ^
      5 * v * U ^ 3 * τ * s ^ 4 * S := by
  linear_combination (T ^ 2 * s * S ^ 2 + τ * T ^ 2 * s ^ 2 * S ^ 2 + τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 2
      + U * V * τ * T ^ 2 * s ^ 2 * S ^ 3 + U * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 3 + v ^ 2 * τ * T ^
      2 * s ^ 2 * S ^ 3 + v ^ 2 * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 3 + v ^ 2 * V * T ^ 3 * s ^ 2 * S ^ 4
      + v ^ 2 * V * τ * T ^ 3 * s ^ 3 * S ^ 4 + v ^ 2 * U * τ * T ^ 2 * s * S ^ 4 + v ^ 2 * U * τ ^
      2 * T ^ 2 * s ^ 2 * S ^ 4 + v ^ 2 * U * τ ^ 3 * T ^ 2 * s ^ 3 * S ^ 4 + v ^ 2 * U * V * τ * T
      ^ 2 * s ^ 2 * S ^ 4 + v ^ 2 * U * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 4 + v ^ 4 * V * τ * T ^ 2 *
      s ^ 3 * S ^ 4 + u * v * T ^ 3 * s ^ 2 * S ^ 3 + u * v * τ * T ^ 3 * s ^ 3 * S ^ 3 + u * v * U
      * τ * T ^ 2 * s ^ 2 * S ^ 3 + u * v * U * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 3 + u * v * U ^ 2 * τ *
      T ^ 2 * s * S ^ 4 + u * v * U ^ 2 * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 4 + u * v * U ^ 2 * τ ^ 3 * T
      ^ 2 * s ^ 3 * S ^ 4 + (2) * u * v * U ^ 2 * V * τ * T ^ 2 * s ^ 2 * S ^ 4 + (2) * u * v * U ^
      2 * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 4 + u * v ^ 3 * τ * T ^ 2 * s ^ 3 * S ^ 3 + u * v ^ 3 * U
      * V * τ * T ^ 2 * s ^ 3 * S ^ 4 + u ^ 2 * U ^ 3 * V * τ * T ^ 2 * s ^ 2 * S ^ 4 + u ^ 2 * U ^
      3 * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 4 + u ^ 2 * v ^ 2 * U * τ * T ^ 2 * s ^ 3 * S ^ 3 + u ^ 2
      * v ^ 2 * U ^ 2 * τ * T ^ 2 * s ^ 2 * S ^ 4 + u ^ 2 * v ^ 2 * U ^ 2 * τ ^ 2 * T ^ 2 * s ^ 3 *
      S ^ 4 + (2) * u ^ 3 * v * U ^ 3 * τ * T ^ 2 * s ^ 2 * S ^ 4 + (2) * u ^ 3 * v * U ^ 3 * τ ^ 2
      * T ^ 2 * s ^ 3 * S ^ 4 + u ^ 4 * U ^ 4 * τ * T ^ 2 * s ^ 2 * S ^ 4 + u ^ 4 * U ^ 4 * τ ^ 2 *
      T ^ 2 * s ^ 3 * S ^ 4) * hts + (s + T * s * S + U * V * τ * s ^ 2 * S + U * V * τ * T * s ^ 2
      * S ^ 2 + (-1) * U * V * τ ^ 3 * T * s ^ 4 * S ^ 2 + v ^ 2 * τ * s ^ 2 * S + v ^ 2 * τ * T * s
      ^ 2 * S ^ 2 + (-1) * v ^ 2 * τ ^ 3 * T * s ^ 4 * S ^ 2 + v ^ 2 * V * T * s ^ 2 * S ^ 2 + v ^ 2
      * V * T ^ 2 * s ^ 2 * S ^ 3 + (-1) * v ^ 2 * V * τ ^ 2 * T * s ^ 4 * S ^ 2 + (-1) * v ^ 2 * V
      * τ ^ 2 * T ^ 2 * s ^ 4 * S ^ 3 + v ^ 2 * V ^ 2 * τ * s ^ 4 * S + v ^ 2 * U * τ * s * S ^ 2 +
      v ^ 2 * U * τ * T * s * S ^ 3 + (-1) * v ^ 2 * U * τ ^ 4 * s ^ 4 * S ^ 2 + (-1) * v ^ 2 * U *
      τ ^ 4 * T * s ^ 4 * S ^ 3 + v ^ 2 * U * V * τ * s ^ 2 * S ^ 2 + v ^ 2 * U * V * τ * T * s ^ 2
      * S ^ 3 + (-1) * v ^ 2 * U * V * τ ^ 3 * s ^ 4 * S ^ 2 + (-1) * v ^ 2 * U * V * τ ^ 3 * T * s
      ^ 4 * S ^ 3 + v ^ 4 * V * τ * s ^ 3 * S ^ 2 + v ^ 4 * V * τ * T * s ^ 3 * S ^ 3 + (-1) * v ^ 4
      * V * τ ^ 2 * s ^ 4 * S ^ 2 + (-1) * v ^ 4 * V * τ ^ 2 * T * s ^ 4 * S ^ 3 + u * v * T * s ^ 2
      * S + u * v * T ^ 2 * s ^ 2 * S ^ 2 + (-1) * u * v * τ ^ 2 * T ^ 2 * s ^ 4 * S ^ 2 + u * v * V
      * τ * s ^ 4 + u * v * V * τ * T * s ^ 4 * S + u * v * U * τ * s ^ 2 * S + u * v * U * τ * T *
      s ^ 2 * S ^ 2 + (-1) * u * v * U * τ ^ 3 * T * s ^ 4 * S ^ 2 + u * v * U ^ 2 * τ * s * S ^ 2 +
      u * v * U ^ 2 * τ * T * s * S ^ 3 + (-1) * u * v * U ^ 2 * τ ^ 4 * s ^ 4 * S ^ 2 + (-1) * u *
      v * U ^ 2 * τ ^ 4 * T * s ^ 4 * S ^ 3 + (2) * u * v * U ^ 2 * V * τ * s ^ 2 * S ^ 2 + (2) * u
      * v * U ^ 2 * V * τ * T * s ^ 2 * S ^ 3 + (-2) * u * v * U ^ 2 * V * τ ^ 3 * s ^ 4 * S ^ 2 +
      (-2) * u * v * U ^ 2 * V * τ ^ 3 * T * s ^ 4 * S ^ 3 + u * v ^ 3 * τ * s ^ 3 * S + u * v ^ 3 *
      τ * T * s ^ 3 * S ^ 2 + (-1) * u * v ^ 3 * τ ^ 2 * T * s ^ 4 * S ^ 2 + u * v ^ 3 * V * τ * s ^
      4 * S + u * v ^ 3 * U * V * τ * s ^ 3 * S ^ 2 + u * v ^ 3 * U * V * τ * T * s ^ 3 * S ^ 3 +
      (-1) * u * v ^ 3 * U * V * τ ^ 2 * s ^ 4 * S ^ 2 + (-1) * u * v ^ 3 * U * V * τ ^ 2 * T * s ^
      4 * S ^ 3 + u ^ 2 * U ^ 3 * V * τ * s ^ 2 * S ^ 2 + u ^ 2 * U ^ 3 * V * τ * T * s ^ 2 * S ^ 3
      + (-1) * u ^ 2 * U ^ 3 * V * τ ^ 3 * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * U ^ 3 * V * τ ^ 3 * T * s
      ^ 4 * S ^ 3 + u ^ 2 * v ^ 2 * U * τ * s ^ 3 * S + u ^ 2 * v ^ 2 * U * τ * T * s ^ 3 * S ^ 2 +
      (-1) * u ^ 2 * v ^ 2 * U * τ ^ 2 * T * s ^ 4 * S ^ 2 + (2) * u ^ 2 * v ^ 2 * U * V * τ * s ^ 4
      * S + u ^ 2 * v ^ 2 * U ^ 2 * τ * s ^ 2 * S ^ 2 + u ^ 2 * v ^ 2 * U ^ 2 * τ * T * s ^ 2 * S ^
      3 + (-1) * u ^ 2 * v ^ 2 * U ^ 2 * τ ^ 3 * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * v ^ 2 * U ^ 2 * τ ^
      3 * T * s ^ 4 * S ^ 3 + u ^ 3 * v * U ^ 2 * V * τ * s ^ 4 * S + (2) * u ^ 3 * v * U ^ 3 * τ *
      s ^ 2 * S ^ 2 + (2) * u ^ 3 * v * U ^ 3 * τ * T * s ^ 2 * S ^ 3 + (-2) * u ^ 3 * v * U ^ 3 * τ
      ^ 3 * s ^ 4 * S ^ 2 + (-2) * u ^ 3 * v * U ^ 3 * τ ^ 3 * T * s ^ 4 * S ^ 3 + u ^ 3 * v ^ 3 * U
      * τ * s ^ 4 * S + u ^ 4 * U ^ 4 * τ * s ^ 2 * S ^ 2 + u ^ 4 * U ^ 4 * τ * T * s ^ 2 * S ^ 3 +
      (-1) * u ^ 4 * U ^ 4 * τ ^ 3 * s ^ 4 * S ^ 2 + (-1) * u ^ 4 * U ^ 4 * τ ^ 3 * T * s ^ 4 * S ^
      3 + (2) * u ^ 4 * v ^ 2 * U ^ 2 * τ * s ^ 4 * S + u ^ 5 * v * U ^ 3 * τ * s ^ 4 * S) * hTS +
      ((-1) * τ ^ 2 * T ^ 2 * s ^ 4 * S ^ 2 + (-1) * V * τ * T ^ 2 * s ^ 4 * S ^ 2 + (-1) * V ^ 2 *
      T ^ 2 * s ^ 4 * S ^ 2 + (-1) * U * V * τ ^ 2 * T * s ^ 4 * S ^ 2 + (-1) * U * V ^ 2 * τ * T *
      s ^ 4 * S ^ 2 + (-1) * U * V ^ 3 * T * s ^ 4 * S ^ 2 + (-1) * v ^ 2 * τ ^ 2 * T * s ^ 4 * S ^
      2 + (-2) * v ^ 2 * V * τ * T * s ^ 4 * S ^ 2 + (-3) * v ^ 2 * V ^ 2 * T * s ^ 4 * S ^ 2 + (-1)
      * v ^ 2 * U * τ ^ 3 * s ^ 4 * S ^ 2 + (-2) * v ^ 2 * U * V * τ ^ 2 * s ^ 4 * S ^ 2 + (-2) * v
      ^ 2 * U * V ^ 2 * τ * s ^ 4 * S ^ 2 + (-2) * v ^ 2 * U * V ^ 3 * s ^ 4 * S ^ 2 + (-1) * v ^ 4
      * V * τ * s ^ 4 * S ^ 2 + (-2) * v ^ 4 * V ^ 2 * s ^ 4 * S ^ 2 + (-2) * u * v * τ * T ^ 2 * s
      ^ 4 * S ^ 2 + (-4) * u * v * V * T ^ 2 * s ^ 4 * S ^ 2 + (-1) * u * v * U * τ ^ 2 * T * s ^ 4
      * S ^ 2 + (-2) * u * v * U * V * τ * T * s ^ 4 * S ^ 2 + (-3) * u * v * U * V ^ 2 * T * s ^ 4
      * S ^ 2 + (-1) * u * v * U ^ 2 * τ ^ 3 * s ^ 4 * S ^ 2 + (-3) * u * v * U ^ 2 * V * τ ^ 2 * s
      ^ 4 * S ^ 2 + (-3) * u * v * U ^ 2 * V ^ 2 * τ * s ^ 4 * S ^ 2 + (-3) * u * v * U ^ 2 * V ^ 3
      * s ^ 4 * S ^ 2 + (-2) * u * v ^ 3 * τ * T * s ^ 4 * S ^ 2 + (-5) * u * v ^ 3 * V * T * s ^ 4
      * S ^ 2 + (-1) * u * v ^ 3 * U * τ ^ 2 * s ^ 4 * S ^ 2 + (-4) * u * v ^ 3 * U * V * τ * s ^ 4
      * S ^ 2 + (-8) * u * v ^ 3 * U * V ^ 2 * s ^ 4 * S ^ 2 + (-1) * u * v ^ 5 * V * s ^ 4 * S ^ 2
      + (-1) * u ^ 2 * U * τ * T ^ 2 * s ^ 4 * S ^ 2 + (-2) * u ^ 2 * U * V * T ^ 2 * s ^ 4 * S ^ 2
      + (-1) * u ^ 2 * U ^ 2 * V * τ * T * s ^ 4 * S ^ 2 + (-2) * u ^ 2 * U ^ 2 * V ^ 2 * T * s ^ 4
      * S ^ 2 + (-1) * u ^ 2 * U ^ 3 * V * τ ^ 2 * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * U ^ 3 * V ^ 2 * τ
      * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * U ^ 3 * V ^ 3 * s ^ 4 * S ^ 2 + (-2) * u ^ 2 * v ^ 2 * T ^ 2
      * s ^ 4 * S ^ 2 + (-3) * u ^ 2 * v ^ 2 * U * τ * T * s ^ 4 * S ^ 2 + (-9) * u ^ 2 * v ^ 2 * U
      * V * T * s ^ 4 * S ^ 2 + (-3) * u ^ 2 * v ^ 2 * U ^ 2 * τ ^ 2 * s ^ 4 * S ^ 2 + (-8) * u ^ 2
      * v ^ 2 * U ^ 2 * V * τ * s ^ 4 * S ^ 2 + (-14) * u ^ 2 * v ^ 2 * U ^ 2 * V ^ 2 * s ^ 4 * S ^
      2 + (-2) * u ^ 2 * v ^ 4 * T * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * v ^ 4 * U * τ * s ^ 4 * S ^ 2 +
      (-7) * u ^ 2 * v ^ 4 * U * V * s ^ 4 * S ^ 2 + (-3) * u ^ 3 * v * U * T ^ 2 * s ^ 4 * S ^ 2 +
      (-1) * u ^ 3 * v * U ^ 2 * τ * T * s ^ 4 * S ^ 2 + (-5) * u ^ 3 * v * U ^ 2 * V * T * s ^ 4 *
      S ^ 2 + (-3) * u ^ 3 * v * U ^ 3 * τ ^ 2 * s ^ 4 * S ^ 2 + (-7) * u ^ 3 * v * U ^ 3 * V * τ *
      s ^ 4 * S ^ 2 + (-11) * u ^ 3 * v * U ^ 3 * V ^ 2 * s ^ 4 * S ^ 2 + (-6) * u ^ 3 * v ^ 3 * U *
      T * s ^ 4 * S ^ 2 + (-4) * u ^ 3 * v ^ 3 * U ^ 2 * τ * s ^ 4 * S ^ 2 + (-18) * u ^ 3 * v ^ 3 *
      U ^ 2 * V * s ^ 4 * S ^ 2 + (-1) * u ^ 3 * v ^ 5 * U * s ^ 4 * S ^ 2 + (-1) * u ^ 4 * U ^ 2 *
      T ^ 2 * s ^ 4 * S ^ 2 + (-1) * u ^ 4 * U ^ 3 * V * T * s ^ 4 * S ^ 2 + (-1) * u ^ 4 * U ^ 4 *
      τ ^ 2 * s ^ 4 * S ^ 2 + (-2) * u ^ 4 * U ^ 4 * V * τ * s ^ 4 * S ^ 2 + (-3) * u ^ 4 * U ^ 4 *
      V ^ 2 * s ^ 4 * S ^ 2 + (-6) * u ^ 4 * v ^ 2 * U ^ 2 * T * s ^ 4 * S ^ 2 + (-6) * u ^ 4 * v ^
      2 * U ^ 3 * τ * s ^ 4 * S ^ 2 + (-22) * u ^ 4 * v ^ 2 * U ^ 3 * V * s ^ 4 * S ^ 2 + (-5) * u ^
      4 * v ^ 4 * U ^ 2 * s ^ 4 * S ^ 2 + (-2) * u ^ 5 * v * U ^ 3 * T * s ^ 4 * S ^ 2 + (-4) * u ^
      5 * v * U ^ 4 * τ * s ^ 4 * S ^ 2 + (-13) * u ^ 5 * v * U ^ 4 * V * s ^ 4 * S ^ 2 + (-10) * u
      ^ 5 * v ^ 3 * U ^ 3 * s ^ 4 * S ^ 2 + (-1) * u ^ 6 * U ^ 5 * τ * s ^ 4 * S ^ 2 + (-3) * u ^ 6
      * U ^ 5 * V * s ^ 4 * S ^ 2 + (-10) * u ^ 6 * v ^ 2 * U ^ 4 * s ^ 4 * S ^ 2 + (-5) * u ^ 7 * v
      * U ^ 5 * s ^ 4 * S ^ 2 + (-1) * u ^ 8 * U ^ 6 * s ^ 4 * S ^ 2) * ht + ((-1) * V ^ 3 * T * s ^
      4 * S ^ 2 + (-2) * U * V ^ 4 * s ^ 4 * S ^ 2 + (-4) * v ^ 2 * V ^ 3 * s ^ 4 * S ^ 2 + (-5) * u
      * v * V ^ 2 * T * s ^ 4 * S ^ 2 + (-9) * u * v * U * V ^ 3 * s ^ 4 * S ^ 2 + (-13) * u * v ^ 3
      * V ^ 2 * s ^ 4 * S ^ 2 + (-3) * u ^ 2 * U * V ^ 2 * T * s ^ 4 * S ^ 2 + (-7) * u ^ 2 * U ^ 2
      * V ^ 3 * s ^ 4 * S ^ 2 + (-6) * u ^ 2 * v ^ 2 * V * T * s ^ 4 * S ^ 2 + (-24) * u ^ 2 * v ^ 2
      * U * V ^ 2 * s ^ 4 * S ^ 2 + (-13) * u ^ 2 * v ^ 4 * V * s ^ 4 * S ^ 2 + (-9) * u ^ 3 * v * U
      * V * T * s ^ 4 * S ^ 2 + (-24) * u ^ 3 * v * U ^ 2 * V ^ 2 * s ^ 4 * S ^ 2 + (-2) * u ^ 3 * v
      ^ 3 * T * s ^ 4 * S ^ 2 + (-31) * u ^ 3 * v ^ 3 * U * V * s ^ 4 * S ^ 2 + (-4) * u ^ 3 * v ^ 5
      * s ^ 4 * S ^ 2 + (-3) * u ^ 4 * U ^ 2 * V * T * s ^ 4 * S ^ 2 + (-9) * u ^ 4 * U ^ 3 * V ^ 2
      * s ^ 4 * S ^ 2 + (-5) * u ^ 4 * v ^ 2 * U * T * s ^ 4 * S ^ 2 + (-34) * u ^ 4 * v ^ 2 * U ^ 2
      * V * s ^ 4 * S ^ 2 + (-13) * u ^ 4 * v ^ 4 * U * s ^ 4 * S ^ 2 + (-4) * u ^ 5 * v * U ^ 2 * T
      * s ^ 4 * S ^ 2 + (-21) * u ^ 5 * v * U ^ 3 * V * s ^ 4 * S ^ 2 + (-18) * u ^ 5 * v ^ 3 * U ^
      2 * s ^ 4 * S ^ 2 + (-1) * u ^ 6 * U ^ 3 * T * s ^ 4 * S ^ 2 + (-5) * u ^ 6 * U ^ 4 * V * s ^
      4 * S ^ 2 + (-14) * u ^ 6 * v ^ 2 * U ^ 3 * s ^ 4 * S ^ 2 + (-6) * u ^ 7 * v * U ^ 4 * s ^ 4 *
      S ^ 2 + (-1) * u ^ 8 * U ^ 5 * s ^ 4 * S ^ 2) * hT + ((-1) * U ^ 2 * V ^ 5 * s ^ 4 * S ^ 2 +
      (-4) * v ^ 2 * U * V ^ 4 * s ^ 4 * S ^ 2 + (-3) * v ^ 4 * V ^ 3 * s ^ 4 * S ^ 2 + (-6) * u * v
      * U ^ 2 * V ^ 4 * s ^ 4 * S ^ 2 + (-16) * u * v ^ 3 * U * V ^ 3 * s ^ 4 * S ^ 2 + (-8) * u * v
      ^ 5 * V ^ 2 * s ^ 4 * S ^ 2 + (-5) * u ^ 2 * U ^ 3 * V ^ 4 * s ^ 4 * S ^ 2 + (-27) * u ^ 2 * v
      ^ 2 * U ^ 2 * V ^ 3 * s ^ 4 * S ^ 2 + (-27) * u ^ 2 * v ^ 4 * U * V ^ 2 * s ^ 4 * S ^ 2 + (-7)
      * u ^ 2 * v ^ 6 * V * s ^ 4 * S ^ 2 + (-24) * u ^ 3 * v * U ^ 3 * V ^ 3 * s ^ 4 * S ^ 2 +
      (-54) * u ^ 3 * v ^ 3 * U ^ 2 * V ^ 2 * s ^ 4 * S ^ 2 + (-22) * u ^ 3 * v ^ 5 * U * V * s ^ 4
      * S ^ 2 + (-2) * u ^ 3 * v ^ 7 * s ^ 4 * S ^ 2 + (-10) * u ^ 4 * U ^ 4 * V ^ 3 * s ^ 4 * S ^ 2
      + (-57) * u ^ 4 * v ^ 2 * U ^ 3 * V ^ 2 * s ^ 4 * S ^ 2 + (-45) * u ^ 4 * v ^ 4 * U ^ 2 * V *
      s ^ 4 * S ^ 2 + (-7) * u ^ 4 * v ^ 6 * U * s ^ 4 * S ^ 2 + (-36) * u ^ 5 * v * U ^ 4 * V ^ 2 *
      s ^ 4 * S ^ 2 + (-60) * u ^ 5 * v ^ 3 * U ^ 3 * V * s ^ 4 * S ^ 2 + (-14) * u ^ 5 * v ^ 5 * U
      ^ 2 * s ^ 4 * S ^ 2 + (-10) * u ^ 6 * U ^ 5 * V ^ 2 * s ^ 4 * S ^ 2 + (-49) * u ^ 6 * v ^ 2 *
      U ^ 4 * V * s ^ 4 * S ^ 2 + (-21) * u ^ 6 * v ^ 4 * U ^ 3 * s ^ 4 * S ^ 2 + (-24) * u ^ 7 * v
      * U ^ 5 * V * s ^ 4 * S ^ 2 + (-22) * u ^ 7 * v ^ 3 * U ^ 4 * s ^ 4 * S ^ 2 + (-5) * u ^ 8 * U
      ^ 6 * V * s ^ 4 * S ^ 2 + (-15) * u ^ 8 * v ^ 2 * U ^ 5 * s ^ 4 * S ^ 2 + (-6) * u ^ 9 * v * U
      ^ 6 * s ^ 4 * S ^ 2 + (-1) * u ^ 10 * U ^ 7 * s ^ 4 * S ^ 2) * h2

theorem suzukiBruhat_entry_31 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = v * τ * s * S + v * V ^ 2 * T * s ^ 2 * S ^ 2 + v * U * τ * S ^ 2 + v * U * V * τ * s * S ^
      2 + v ^ 3 * V * τ * s ^ 2 * S ^ 2 + v ^ 3 * V ^ 2 * τ * s ^ 3 * S ^ 2 + u * V * T * s ^ 2 * S
      + u * U ^ 2 * V * τ * s * S ^ 2 + u * v ^ 2 * τ * s ^ 2 * S + u * v ^ 2 * V * τ * s ^ 3 * S +
      u * v ^ 2 * U * V ^ 2 * τ * s ^ 3 * S ^ 2 + u ^ 2 * v * U * V * T * s ^ 2 * S ^ 2 + u ^ 2 * v
      * U * V * τ * s ^ 3 * S + u ^ 2 * v * U ^ 2 * τ * s * S ^ 2 + u ^ 2 * v ^ 3 * U * V * τ * s ^
      3 * S ^ 2 + u ^ 3 * U * T * s ^ 2 * S + u ^ 3 * U ^ 3 * τ * s * S ^ 2 + u ^ 3 * v ^ 2 * U * τ
      * s ^ 3 * S + u ^ 3 * v ^ 2 * U ^ 2 * V * τ * s ^ 3 * S ^ 2 + u ^ 4 * v * U ^ 2 * τ * s ^ 3 *
      S := by
  linear_combination (v * τ * T ^ 2 * s * S ^ 3 + v * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 3 + v * V ^ 2 * T
      ^ 3 * s ^ 2 * S ^ 4 + v * U * τ * T ^ 2 * S ^ 4 + v * U * τ ^ 2 * T ^ 2 * s * S ^ 4 + v * U *
      τ ^ 3 * T ^ 2 * s ^ 2 * S ^ 4 + v * U * V * τ * T ^ 2 * s * S ^ 4 + v * U * V * τ ^ 2 * T ^ 2
      * s ^ 2 * S ^ 4 + v ^ 3 * V * τ * T ^ 2 * s ^ 2 * S ^ 4 + u * V * T ^ 3 * s ^ 2 * S ^ 3 + u *
      U ^ 2 * V * τ * T ^ 2 * s * S ^ 4 + u * U ^ 2 * V * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 4 + u * v ^ 2
      * τ * T ^ 2 * s ^ 2 * S ^ 3 + u ^ 2 * v * U * V * T ^ 3 * s ^ 2 * S ^ 4 + u ^ 2 * v * U ^ 2 *
      τ * T ^ 2 * s * S ^ 4 + u ^ 2 * v * U ^ 2 * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 4 + u ^ 3 * U * T ^ 3
      * s ^ 2 * S ^ 3 + u ^ 3 * U ^ 3 * τ * T ^ 2 * s * S ^ 4 + u ^ 3 * U ^ 3 * τ ^ 2 * T ^ 2 * s ^
      2 * S ^ 4) * hts + (v * τ * s * S + v * τ * T * s * S ^ 2 + (-1) * v * τ ^ 3 * T * s ^ 3 * S ^
      2 + v * V ^ 2 * T * s ^ 2 * S ^ 2 + v * V ^ 2 * T ^ 2 * s ^ 2 * S ^ 3 + (-1) * v * V ^ 2 * τ *
      T * s ^ 3 * S ^ 2 + (-1) * v * V ^ 2 * τ * T ^ 2 * s ^ 3 * S ^ 3 + v * U * τ * S ^ 2 + v * U *
      τ * T * S ^ 3 + (-1) * v * U * τ ^ 4 * s ^ 3 * S ^ 2 + (-1) * v * U * τ ^ 4 * T * s ^ 3 * S ^
      3 + v * U * V * τ * s * S ^ 2 + v * U * V * τ * T * s * S ^ 3 + (-1) * v * U * V * τ ^ 3 * s ^
      3 * S ^ 2 + (-1) * v * U * V * τ ^ 3 * T * s ^ 3 * S ^ 3 + v ^ 3 * V * τ * s ^ 2 * S ^ 2 + v ^
      3 * V * τ * T * s ^ 2 * S ^ 3 + (-1) * v ^ 3 * V * τ ^ 2 * s ^ 3 * S ^ 2 + (-1) * v ^ 3 * V *
      τ ^ 2 * T * s ^ 3 * S ^ 3 + u * V * T * s ^ 2 * S + u * V * T ^ 2 * s ^ 2 * S ^ 2 + (-1) * u *
      V * τ * T ^ 2 * s ^ 3 * S ^ 2 + u * U ^ 2 * V * τ * s * S ^ 2 + u * U ^ 2 * V * τ * T * s * S
      ^ 3 + (-1) * u * U ^ 2 * V * τ ^ 3 * s ^ 3 * S ^ 2 + (-1) * u * U ^ 2 * V * τ ^ 3 * T * s ^ 3
      * S ^ 3 + u * v ^ 2 * τ * s ^ 2 * S + u * v ^ 2 * τ * T * s ^ 2 * S ^ 2 + (-1) * u * v ^ 2 * τ
      ^ 2 * T * s ^ 3 * S ^ 2 + u * v ^ 2 * V * τ * s ^ 3 * S + u ^ 2 * v * U * V * T * s ^ 2 * S ^
      2 + u ^ 2 * v * U * V * T ^ 2 * s ^ 2 * S ^ 3 + u ^ 2 * v * U * V * τ * s ^ 3 * S + (-1) * u ^
      2 * v * U * V * τ * T * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * U * V * τ * T ^ 2 * s ^ 3 * S ^ 3 +
      u ^ 2 * v * U ^ 2 * τ * s * S ^ 2 + u ^ 2 * v * U ^ 2 * τ * T * s * S ^ 3 + (-1) * u ^ 2 * v *
      U ^ 2 * τ ^ 3 * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * U ^ 2 * τ ^ 3 * T * s ^ 3 * S ^ 3 + u ^ 3 *
      U * T * s ^ 2 * S + u ^ 3 * U * T ^ 2 * s ^ 2 * S ^ 2 + (-1) * u ^ 3 * U * τ * T ^ 2 * s ^ 3 *
      S ^ 2 + u ^ 3 * U ^ 3 * τ * s * S ^ 2 + u ^ 3 * U ^ 3 * τ * T * s * S ^ 3 + (-1) * u ^ 3 * U ^
      3 * τ ^ 3 * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * U ^ 3 * τ ^ 3 * T * s ^ 3 * S ^ 3 + u ^ 3 * v ^ 2 *
      U * τ * s ^ 3 * S + u ^ 4 * v * U ^ 2 * τ * s ^ 3 * S) * hTS + ((-1) * v * τ ^ 2 * T * s ^ 3 *
      S ^ 2 + (-1) * v * V * τ * T * s ^ 3 * S ^ 2 + (-2) * v * V ^ 2 * T * s ^ 3 * S ^ 2 + (-1) * v
      * U * τ ^ 3 * s ^ 3 * S ^ 2 + (-2) * v * U * V * τ ^ 2 * s ^ 3 * S ^ 2 + (-2) * v * U * V ^ 2
      * τ * s ^ 3 * S ^ 2 + (-2) * v * U * V ^ 3 * s ^ 3 * S ^ 2 + (-1) * v ^ 3 * V * τ * s ^ 3 * S
      ^ 2 + (-2) * v ^ 3 * V ^ 2 * s ^ 3 * S ^ 2 + (-1) * u * V * T ^ 2 * s ^ 3 * S ^ 2 + (-1) * u *
      U ^ 2 * V * τ ^ 2 * s ^ 3 * S ^ 2 + (-1) * u * U ^ 2 * V ^ 2 * τ * s ^ 3 * S ^ 2 + (-1) * u *
      U ^ 2 * V ^ 3 * s ^ 3 * S ^ 2 + (-2) * u * v ^ 2 * τ * T * s ^ 3 * S ^ 2 + (-4) * u * v ^ 2 *
      V * T * s ^ 3 * S ^ 2 + (-1) * u * v ^ 2 * U * τ ^ 2 * s ^ 3 * S ^ 2 + (-3) * u * v ^ 2 * U *
      V * τ * s ^ 3 * S ^ 2 + (-6) * u * v ^ 2 * U * V ^ 2 * s ^ 3 * S ^ 2 + (-1) * u * v ^ 4 * V *
      s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * U * τ * T * s ^ 3 * S ^ 2 + (-4) * u ^ 2 * v * U * V * T *
      s ^ 3 * S ^ 2 + (-2) * u ^ 2 * v * U ^ 2 * τ ^ 2 * s ^ 3 * S ^ 2 + (-5) * u ^ 2 * v * U ^ 2 *
      V * τ * s ^ 3 * S ^ 2 + (-8) * u ^ 2 * v * U ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 + (-2) * u ^ 2 * v ^
      3 * T * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v ^ 3 * U * τ * s ^ 3 * S ^ 2 + (-6) * u ^ 2 * v ^ 3 *
      U * V * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * U * T ^ 2 * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * U ^ 3 * τ ^
      2 * s ^ 3 * S ^ 2 + (-2) * u ^ 3 * U ^ 3 * V * τ * s ^ 3 * S ^ 2 + (-3) * u ^ 3 * U ^ 3 * V ^
      2 * s ^ 3 * S ^ 2 + (-4) * u ^ 3 * v ^ 2 * U * T * s ^ 3 * S ^ 2 + (-3) * u ^ 3 * v ^ 2 * U ^
      2 * τ * s ^ 3 * S ^ 2 + (-12) * u ^ 3 * v ^ 2 * U ^ 2 * V * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * v ^
      4 * U * s ^ 3 * S ^ 2 + (-2) * u ^ 4 * v * U ^ 2 * T * s ^ 3 * S ^ 2 + (-3) * u ^ 4 * v * U ^
      3 * τ * s ^ 3 * S ^ 2 + (-10) * u ^ 4 * v * U ^ 3 * V * s ^ 3 * S ^ 2 + (-4) * u ^ 4 * v ^ 3 *
      U ^ 2 * s ^ 3 * S ^ 2 + (-1) * u ^ 5 * U ^ 4 * τ * s ^ 3 * S ^ 2 + (-3) * u ^ 5 * U ^ 4 * V *
      s ^ 3 * S ^ 2 + (-6) * u ^ 5 * v ^ 2 * U ^ 3 * s ^ 3 * S ^ 2 + (-4) * u ^ 6 * v * U ^ 4 * s ^
      3 * S ^ 2 + (-1) * u ^ 7 * U ^ 5 * s ^ 3 * S ^ 2) * ht + ((-2) * v * V ^ 3 * s ^ 3 * S ^ 2 +
      (-1) * u * V ^ 2 * T * s ^ 3 * S ^ 2 + (-1) * u * U * V ^ 3 * s ^ 3 * S ^ 2 + (-7) * u * v ^ 2
      * V ^ 2 * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * V * T * s ^ 3 * S ^ 2 + (-7) * u ^ 2 * v * U * V
      ^ 2 * s ^ 3 * S ^ 2 + (-7) * u ^ 2 * v ^ 3 * V * s ^ 3 * S ^ 2 + (-2) * u ^ 3 * U * V * T * s
      ^ 3 * S ^ 2 + (-3) * u ^ 3 * U ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 + (-14) * u ^ 3 * v ^ 2 * U * V * s
      ^ 3 * S ^ 2 + (-2) * u ^ 3 * v ^ 4 * s ^ 3 * S ^ 2 + (-1) * u ^ 4 * v * U * T * s ^ 3 * S ^ 2
      + (-8) * u ^ 4 * v * U ^ 2 * V * s ^ 3 * S ^ 2 + (-7) * u ^ 4 * v ^ 3 * U * s ^ 3 * S ^ 2 +
      (-1) * u ^ 5 * U ^ 2 * T * s ^ 3 * S ^ 2 + (-3) * u ^ 5 * U ^ 3 * V * s ^ 3 * S ^ 2 + (-7) * u
      ^ 5 * v ^ 2 * U ^ 2 * s ^ 3 * S ^ 2 + (-3) * u ^ 6 * v * U ^ 3 * s ^ 3 * S ^ 2 + (-1) * u ^ 7
      * U ^ 4 * s ^ 3 * S ^ 2) * hT + ((-2) * v * U * V ^ 4 * s ^ 3 * S ^ 2 + (-2) * v ^ 3 * V ^ 3 *
      s ^ 3 * S ^ 2 + (-1) * u * U ^ 2 * V ^ 4 * s ^ 3 * S ^ 2 + (-8) * u * v ^ 2 * U * V ^ 3 * s ^
      3 * S ^ 2 + (-5) * u * v ^ 4 * V ^ 2 * s ^ 3 * S ^ 2 + (-10) * u ^ 2 * v * U ^ 2 * V ^ 3 * s ^
      3 * S ^ 2 + (-14) * u ^ 2 * v ^ 3 * U * V ^ 2 * s ^ 3 * S ^ 2 + (-4) * u ^ 2 * v ^ 5 * V * s ^
      3 * S ^ 2 + (-4) * u ^ 3 * U ^ 3 * V ^ 3 * s ^ 3 * S ^ 2 + (-25) * u ^ 3 * v ^ 2 * U ^ 2 * V ^
      2 * s ^ 3 * S ^ 2 + (-12) * u ^ 3 * v ^ 4 * U * V * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * v ^ 6 * s ^
      3 * S ^ 2 + (-18) * u ^ 4 * v * U ^ 3 * V ^ 2 * s ^ 3 * S ^ 2 + (-22) * u ^ 4 * v ^ 3 * U ^ 2
      * V * s ^ 3 * S ^ 2 + (-4) * u ^ 4 * v ^ 5 * U * s ^ 3 * S ^ 2 + (-6) * u ^ 5 * U ^ 4 * V ^ 2
      * s ^ 3 * S ^ 2 + (-26) * u ^ 5 * v ^ 2 * U ^ 3 * V * s ^ 3 * S ^ 2 + (-7) * u ^ 5 * v ^ 4 * U
      ^ 2 * s ^ 3 * S ^ 2 + (-14) * u ^ 6 * v * U ^ 4 * V * s ^ 3 * S ^ 2 + (-10) * u ^ 6 * v ^ 3 *
      U ^ 3 * s ^ 3 * S ^ 2 + (-4) * u ^ 7 * U ^ 5 * V * s ^ 3 * S ^ 2 + (-9) * u ^ 7 * v ^ 2 * U ^
      4 * s ^ 3 * S ^ 2 + (-4) * u ^ 8 * v * U ^ 5 * s ^ 3 * S ^ 2 + (-1) * u ^ 9 * U ^ 6 * s ^ 3 *
      S ^ 2) * h2

theorem suzukiBruhat_entry_32 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = v * V * T * s ^ 2 * S + v * U * τ * s * S + v ^ 3 * V * τ * s ^ 3 * S + u * T * s ^ 2 + u *
      U ^ 2 * τ * s * S + u * v ^ 2 * τ * s ^ 3 + u * v ^ 2 * U * V * τ * s ^ 3 * S + u ^ 2 * v * U
      * τ * s ^ 3 := by
  linear_combination (v * V * T ^ 2 * s ^ 2 * S ^ 2 + v * U * τ * T * s * S ^ 2 + v * U * τ ^ 2 * T
      * s ^ 2 * S ^ 2 + u * T ^ 2 * s ^ 2 * S + u * U ^ 2 * τ * T * s * S ^ 2 + u * U ^ 2 * τ ^ 2 *
      T * s ^ 2 * S ^ 2) * hts + (v * V * T * s ^ 2 * S + (-1) * v * V * τ * T * s ^ 3 * S + v * U *
      τ * s * S + (-1) * v * U * τ ^ 3 * s ^ 3 * S + u * T * s ^ 2 + u * U ^ 2 * τ * s * S + (-1) *
      u * U ^ 2 * τ ^ 3 * s ^ 3 * S + u * v ^ 2 * τ * s ^ 3 + u ^ 2 * v * U * τ * s ^ 3) * hTS +
      ((-1) * v * V * T * s ^ 3 * S + (-1) * v * U * τ ^ 2 * s ^ 3 * S + (-1) * v * U * V * τ * s ^
      3 * S + (-1) * v * U * V ^ 2 * s ^ 3 * S + (-1) * v ^ 3 * V * s ^ 3 * S + (-1) * u * T ^ 2 * s
      ^ 3 * S + (-1) * u * U ^ 2 * τ ^ 2 * s ^ 3 * S + (-1) * u * U ^ 2 * V * τ * s ^ 3 * S + (-1) *
      u * U ^ 2 * V ^ 2 * s ^ 3 * S + (-1) * u * v ^ 2 * T * s ^ 3 * S + (-1) * u * v ^ 2 * U * τ *
      s ^ 3 * S + (-3) * u * v ^ 2 * U * V * s ^ 3 * S + (-1) * u ^ 2 * v * U * T * s ^ 3 * S + (-2)
      * u ^ 2 * v * U ^ 2 * τ * s ^ 3 * S + (-4) * u ^ 2 * v * U ^ 2 * V * s ^ 3 * S + (-1) * u ^ 2
      * v ^ 3 * U * s ^ 3 * S + (-1) * u ^ 3 * U ^ 3 * τ * s ^ 3 * S + (-2) * u ^ 3 * U ^ 3 * V * s
      ^ 3 * S + (-3) * u ^ 3 * v ^ 2 * U ^ 2 * s ^ 3 * S + (-3) * u ^ 4 * v * U ^ 3 * s ^ 3 * S +
      (-1) * u ^ 5 * U ^ 4 * s ^ 3 * S) * ht + ((-1) * v * V ^ 2 * s ^ 3 * S + (-1) * u * V * T * s
      ^ 3 * S + (-1) * u * U * V ^ 2 * s ^ 3 * S + (-3) * u * v ^ 2 * V * s ^ 3 * S + (-1) * u ^ 2 *
      v * T * s ^ 3 * S + (-3) * u ^ 2 * v * U * V * s ^ 3 * S + (-2) * u ^ 2 * v ^ 3 * s ^ 3 * S +
      (-1) * u ^ 3 * U * T * s ^ 3 * S + (-2) * u ^ 3 * U ^ 2 * V * s ^ 3 * S + (-3) * u ^ 3 * v ^ 2
      * U * s ^ 3 * S + (-2) * u ^ 4 * v * U ^ 2 * s ^ 3 * S + (-1) * u ^ 5 * U ^ 3 * s ^ 3 * S) *
      hT + ((-1) * v * U * V ^ 3 * s ^ 3 * S + (-1) * v ^ 3 * V ^ 2 * s ^ 3 * S + (-1) * u * U ^ 2 *
      V ^ 3 * s ^ 3 * S + (-4) * u * v ^ 2 * U * V ^ 2 * s ^ 3 * S + (-2) * u * v ^ 4 * V * s ^ 3 *
      S + (-5) * u ^ 2 * v * U ^ 2 * V ^ 2 * s ^ 3 * S + (-5) * u ^ 2 * v ^ 3 * U * V * s ^ 3 * S +
      (-1) * u ^ 2 * v ^ 5 * s ^ 3 * S + (-3) * u ^ 3 * U ^ 3 * V ^ 2 * s ^ 3 * S + (-9) * u ^ 3 * v
      ^ 2 * U ^ 2 * V * s ^ 3 * S + (-2) * u ^ 3 * v ^ 4 * U * s ^ 3 * S + (-7) * u ^ 4 * v * U ^ 3
      * V * s ^ 3 * S + (-4) * u ^ 4 * v ^ 3 * U ^ 2 * s ^ 3 * S + (-3) * u ^ 5 * U ^ 4 * V * s ^ 3
      * S + (-5) * u ^ 5 * v ^ 2 * U ^ 3 * s ^ 3 * S + (-3) * u ^ 6 * v * U ^ 4 * s ^ 3 * S + (-1) *
      u ^ 7 * U ^ 5 * s ^ 3 * S) * h2

theorem suzukiBruhat_entry_33 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    (1) = U * τ * S + v ^ 2 * V * τ * s ^ 2 * S + u * v * τ * s ^ 2 := by
  linear_combination ((-1) * T * S + (-1) * τ * T * s * S + U * τ * T * S ^ 2 + U * τ ^ 2 * T * s *
      S ^ 2) * hts + ((-1) + U * τ * S + (-1) * U * τ ^ 3 * s ^ 2 * S + u * v * τ * s ^ 2) * hTS +
      (τ * T * s ^ 2 * S + V * T * s ^ 2 * S + (-1) * U * τ ^ 2 * s ^ 2 * S + (-1) * U * V * τ * s ^
      2 * S + (-1) * U * V ^ 2 * s ^ 2 * S + (-1) * v ^ 2 * V * s ^ 2 * S + (-1) * u * v * U * τ * s
      ^ 2 * S + (-2) * u * v * U * V * s ^ 2 * S + u ^ 2 * U * T * s ^ 2 * S + (-1) * u ^ 2 * U ^ 2
      * τ * s ^ 2 * S + (-2) * u ^ 2 * U ^ 2 * V * s ^ 2 * S + (-1) * u ^ 2 * v ^ 2 * U * s ^ 2 * S
      + (-2) * u ^ 3 * v * U ^ 2 * s ^ 2 * S + (-1) * u ^ 4 * U ^ 3 * s ^ 2 * S) * ht + (V ^ 2 * s ^
      2 * S + u * v * V * s ^ 2 * S + (2) * u ^ 2 * U * V * s ^ 2 * S + u ^ 3 * v * U * s ^ 2 * S +
      u ^ 4 * U ^ 2 * s ^ 2 * S) * hT + ((-1) * u * v * U * V ^ 2 * s ^ 2 * S + (-1) * u ^ 2 * v ^ 2
      * U * V * s ^ 2 * S + (-2) * u ^ 3 * v * U ^ 2 * V * s ^ 2 * S + (-1) * u ^ 4 * v ^ 2 * U ^ 2
      * s ^ 2 * S + (-1) * u ^ 5 * v * U ^ 3 * s ^ 2 * S) * h2

theorem suzuki_bruhat_factorization [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K)
    (huv : (u, v) ≠ (0, 0)) :
    suzukiN a u v ≠ 0 ∧ ∀ t : Kˣ, (t : K) = suzukiN a u v →
      suzukiW K * suzukiS a u v * suzukiW K =
        suzukiS a (v / t) (u / t) * suzukiD a (t ^ (2 - 2 ^ (a + 1) : ℤ)) * suzukiW K *
          suzukiS a ((u ^ (2 ^ (a + 1) + 1) + v) / t) (v / (t : K) ^ 2 ^ (a + 1)) := by
  refine ⟨fun h => huv (Prod.ext
    ((suzuki_norm_nonzero (a := a) (K := K) hK u v).1 h).1
    ((suzuki_norm_nonzero (a := a) (K := K) hK u v).1 h).2),
    fun t htN => ?_⟩
  obtain ⟨h2, hadd, hθθ⟩ := suzuki_frob_data (a := a) hK
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have hts : (t : K) * (t : K)⁻¹ = 1 := mul_inv_cancel₀ ht0
  have hTS : (t : K) ^ 2 ^ (a + 1) * ((t : K) ^ 2 ^ (a + 1))⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ ht0)
  have ht : (t : K) = u ^ 2 ^ (a + 1) * u ^ 2 + u * v + v ^ 2 ^ (a + 1) := by
    rw [htN, suzukiN, pow_add]
  have hT : (t : K) ^ 2 ^ (a + 1) =
      (u ^ 2 ^ (a + 1)) ^ 2 * u ^ 2 + u ^ 2 ^ (a + 1) * v ^ 2 ^ (a + 1) + v ^ 2 := by
    rw [ht, hadd, hadd, mul_pow, mul_pow, hθθ, hθθ, ← pow_mul, ← pow_mul, mul_comm 2, pow_mul]
    ring
  have hS0 := suzukiS_eq_explicit u v (u ^ 2 ^ (a + 1)) (v ^ 2 ^ (a + 1)) rfl rfl
  have hS1 := suzukiS_eq_explicit (a := a) (v * (t : K)⁻¹) (u * (t : K)⁻¹)
    (v ^ 2 ^ (a + 1) * ((t : K) ^ 2 ^ (a + 1))⁻¹) (u ^ 2 ^ (a + 1) * ((t : K) ^ 2 ^ (a + 1))⁻¹)
    (by rw [mul_pow, inv_pow]) (by rw [mul_pow, inv_pow])
  have hS2 := suzukiS_eq_explicit (a := a) ((u ^ 2 ^ (a + 1) * u + v) * (t : K)⁻¹)
    (v * ((t : K) ^ 2 ^ (a + 1))⁻¹)
    ((u ^ 2 ^ (a + 1) * u ^ 2 + v ^ 2 ^ (a + 1)) * ((t : K) ^ 2 ^ (a + 1))⁻¹)
    (v ^ 2 ^ (a + 1) * ((t : K)⁻¹) ^ 2)
    (by rw [mul_pow, hadd, mul_pow, hθθ, inv_pow]; ring)
    (by rw [mul_pow, inv_pow, hθθ, inv_pow])
  simp only [div_eq_mul_inv]
  rw [pow_succ u (2 ^ (a + 1)), hS0, hS1, hS2, suzukiD_two_sub_theta hK, suzukiW_eq]
  generalize ((t : K) ^ 2 ^ (a + 1))⁻¹ = S at hTS ⊢
  generalize (t : K) ^ 2 ^ (a + 1) = T at hTS hT ⊢
  generalize (t : K)⁻¹ = s at hts ⊢
  generalize u ^ 2 ^ (a + 1) = U at ht hT ⊢
  generalize v ^ 2 ^ (a + 1) = V at ht hT ⊢
  generalize (t : K) = τ at hts ht ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  · linear_combination suzukiBruhat_entry_00 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_01 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_02 u v U τ s hts
  · linear_combination suzukiBruhat_entry_03 u v U V τ ht
  · linear_combination suzukiBruhat_entry_10 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_11 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_12 u v U V τ T s hts ht hT h2
  · linear_combination suzukiBruhat_entry_13 v τ s hts
  · linear_combination suzukiBruhat_entry_20 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_21 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_22 u v U V τ T s S hts hTS ht
  · linear_combination suzukiBruhat_entry_23 u τ s hts
  · linear_combination suzukiBruhat_entry_30 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_31 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_32 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_33 u v U V τ T s S hts hTS ht hT h2


/-! ## Transport to the local transpose-operator presentation -/

/-- The nonzero Suzuki Weyl–root factorization on the actual upper-root and
torus operators in `GL (Fin 4) K`. It is the transpose transport of the
matrix identity above; the product order reverses under transpose. -/
theorem suzukiWeyl_upperRoot_weyl_factorization [Finite K]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K)
    (huv : (u, v) ≠ (0, 0)) :
    let n := suzukiN a u v
    let t : Kˣ := Units.mk0 n
      (by
        intro hn
        have hz := (suzukiNorm_eq_zero_iff a hK u v).mp hn
        exact huv (Prod.ext hz.1 hz.2))
    suzukiWeylOperator * upperRootOperator a u v * suzukiWeylOperator =
      upperRootOperator a ((u ^ (2 ^ (a + 1) + 1) + v) / t)
          (v / (t : K) ^ 2 ^ (a + 1)) *
        suzukiWeylOperator * suzukiTorusOperator a
          (t ^ (2 - 2 ^ (a + 1) : ℤ)) *
        upperRootOperator a (v / t) (u / t) := by
  dsimp
  let t : Kˣ := Units.mk0 (suzukiN a u v)
    (by
      intro hn
      have hz := (suzukiNorm_eq_zero_iff a hK u v).mp hn
      exact huv (Prod.ext hz.1 hz.2))
  have ht : (t : K) = suzukiN a u v := rfl
  have hfactor := (suzuki_bruhat_factorization (a := a) hK u v huv).2 t ht
  have hw : suzukiWeylMatrix (K := K) = suzukiW K :=
    suzukiWeylMatrix_eq_catalog (K := K)
  have hWt : (suzukiW K).transpose = suzukiW K := by
    ext i j
    simp [Chevalley.suzukiW, Matrix.transpose_apply, Nat.add_comm]
  have hDt (l : Kˣ) : (suzukiD a l).transpose = suzukiD a l := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [suzukiD, Matrix.diagonal_apply]
    · have hji : j ≠ i := Ne.symm hij
      simp [suzukiD, Matrix.diagonal_apply, hij, hji]
  apply Units.ext
  simp only [Units.val_mul, coe_suzukiWeylOperator,
    coe_upperRootOperator, coe_suzukiTorusOperator]
  change suzukiWeylMatrix * (suzukiS a u v).transpose * suzukiWeylMatrix =
    (suzukiS a ((u ^ (2 ^ (a + 1) + 1) + v) / t)
        (v / (t : K) ^ 2 ^ (a + 1))).transpose *
      suzukiWeylMatrix * suzukiD a (t ^ (2 - 2 ^ (a + 1) : ℤ)) *
        (suzukiS a (v / t) (u / t)).transpose
  calc
    suzukiWeylMatrix * (suzukiS a u v).transpose * suzukiWeylMatrix =
        (suzukiW K * suzukiS a u v * suzukiW K).transpose := by
          rw [hw]
          simp [Matrix.transpose_mul, hWt, Matrix.mul_assoc]
    _ = (suzukiS a (v / t) (u / t) *
          suzukiD a (t ^ (2 - 2 ^ (a + 1) : ℤ)) * suzukiW K *
          suzukiS a ((u ^ (2 ^ (a + 1) + 1) + v) / t)
            (v / (t : K) ^ 2 ^ (a + 1))).transpose :=
          congrArg Matrix.transpose hfactor
    _ = (suzukiS a ((u ^ (2 ^ (a + 1) + 1) + v) / t)
          (v / (t : K) ^ 2 ^ (a + 1))).transpose *
        suzukiWeylMatrix * suzukiD a (t ^ (2 - 2 ^ (a + 1) : ℤ)) *
          (suzukiS a (v / t) (u / t)).transpose := by
          rw [hw]
          simp [Matrix.transpose_mul, hWt, hDt, Matrix.mul_assoc]

theorem upperRoot_mem_suzukiUpperMatrixGroup (a : ℕ) (x y : K) :
    upperRootOperator a x y ∈ Chevalley.suzukiUpperMatrixGroup a K := by
  apply Subgroup.subset_closure
  change ((upperRootOperator a x y : Matrix.GeneralLinearGroup (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K).transpose ∈
      {M | (∃ p q : K, M = suzukiS a p q) ∨
        (∃ m : Kˣ, M = suzukiD a m) ∨ M = suzukiW K}
  exact Or.inl ⟨x, y, by simp [upperRootOperator, suzukiSGL]⟩

/-- The Weyl–root factorization with the norm witness reduced away, for use in
ordinary existential elimination downstream. -/
theorem exists_suzukiWeyl_upperRoot_weyl_factorization [Finite K]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K)
    (huv : (u, v) ≠ (0, 0)) :
    ∃ x y : K, ∃ l : Kˣ, ∃ c d : K,
      suzukiWeylOperator * upperRootOperator a u v * suzukiWeylOperator =
        upperRootOperator a x y * suzukiWeylOperator * suzukiTorusOperator a l *
          upperRootOperator a c d := by
  let n := suzukiN a u v
  have hn : n ≠ 0 := by
    intro hz
    have hz' := (suzukiNorm_eq_zero_iff a hK u v).mp hz
    exact huv (Prod.ext hz'.1 hz'.2)
  let t : Kˣ := Units.mk0 n hn
  refine ⟨(u ^ (2 ^ (a + 1) + 1) + v) / n,
    v / n ^ 2 ^ (a + 1), t ^ (2 - 2 ^ (a + 1) : ℤ), v / n, u / n, ?_⟩
  dsimp [n, t]
  exact suzukiWeyl_upperRoot_weyl_factorization (K := K) a hK u v huv

/-- The nonzero Weyl–root factorization holds internally in the generated
Suzuki operator group, not just in the ambient general linear group. This is
the local group-level input to the two-cell Bruhat normal-form induction. -/
theorem exists_suzukiGroup_W_root_W_factorization [Finite K]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K)
    (huv : (u, v) ≠ (0, 0)) :
    ∃ x y : K, ∃ l : Kˣ, ∃ c d : K,
      let S := Chevalley.suzukiUpperMatrixGroup a K
      (⟨suzukiWeylOperator (K := K),
          suzukiWeylOperator_mem_suzukiUpperMatrixGroup (K := K) a⟩ : S) *
        ⟨upperRootOperator a u v, upperRoot_mem_suzukiUpperMatrixGroup a u v⟩ *
        ⟨suzukiWeylOperator (K := K),
          suzukiWeylOperator_mem_suzukiUpperMatrixGroup (K := K) a⟩ =
      ⟨upperRootOperator a x y, upperRoot_mem_suzukiUpperMatrixGroup a x y⟩ *
        ⟨suzukiWeylOperator (K := K),
          suzukiWeylOperator_mem_suzukiUpperMatrixGroup (K := K) a⟩ *
        ⟨suzukiTorusOperator a l,
          suzukiTorusOperator_mem_suzukiUpperMatrixGroup (K := K) a l⟩ *
        ⟨upperRootOperator a c d, upperRoot_mem_suzukiUpperMatrixGroup a c d⟩ := by
  let n := suzukiN a u v
  have hn : n ≠ 0 := by
    intro hz
    have hz' := (suzukiNorm_eq_zero_iff a hK u v).mp hz
    exact huv (Prod.ext hz'.1 hz'.2)
  let t : Kˣ := Units.mk0 n hn
  refine ⟨(u ^ (2 ^ (a + 1) + 1) + v) / n,
    v / n ^ 2 ^ (a + 1), t ^ (2 - 2 ^ (a + 1) : ℤ), v / n, u / n, ?_⟩
  dsimp
  apply Subtype.ext
  simpa [t, n] using
    (suzukiWeyl_upperRoot_weyl_factorization (K := K) a hK u v huv)

/-- The local big Bruhat cell `B w U`, where `B` is the generated root–torus
subgroup and `U` is the upper-root operator subgroup. -/
def suzukiBigCellOperatorGroup (a : ℕ) :
    Set (Matrix.GeneralLinearGroup (Fin 4) K) :=
  {g | ∃ b ∈ suzukiPointStabilizerOperatorGroup (K := K) a,
    ∃ x ∈ upperRootMatrixGroup (K := K) a,
      g = b * suzukiWeylOperator (K := K) * x}

/-- Right multiplication by an upper-root operator preserves the union of
the Borel cell and the big Bruhat cell. This is the first generator-stability
step in the external two-cell normal-form induction. -/
theorem mul_mem_suzukiBorelOrBigCell_of_upperRoot [Finite K]
    {a : ℕ} {g x : Matrix.GeneralLinearGroup (Fin 4) K}
    (hg : g ∈ (suzukiPointStabilizerOperatorGroup (K := K) a : Set _) ∪
      suzukiBigCellOperatorGroup (K := K) a)
    (hx : x ∈ upperRootMatrixGroup (K := K) a) :
    g * x ∈ (suzukiPointStabilizerOperatorGroup (K := K) a : Set _) ∪
      suzukiBigCellOperatorGroup (K := K) a := by
  rcases hg with hg | ⟨b, hb, y, hy, rfl⟩
  · exact Or.inl (mul_mem hg
      (upperRootMatrixGroup_le_suzukiPointStabilizerOperatorGroup (K := K) a hx))
  · right
    refine ⟨b, hb, y * x, mul_mem hy hx, ?_⟩
    simp only [mul_assoc]

/-- Right multiplication by a local Suzuki torus generator preserves the
union of the Borel cell and the big Bruhat cell. The big-cell case uses that
the torus normalizes the root subgroup and the Weyl operator inverts the
torus. -/
theorem mul_mem_suzukiBorelOrBigCell_of_torus [Finite K]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    {g : Matrix.GeneralLinearGroup (Fin 4) K}
    (hg : g ∈ (suzukiPointStabilizerOperatorGroup (K := K) a : Set _) ∪
      suzukiBigCellOperatorGroup (K := K) a) (l : Kˣ) :
    g * suzukiTorusOperator a l ∈
      (suzukiPointStabilizerOperatorGroup (K := K) a : Set _) ∪
        suzukiBigCellOperatorGroup (K := K) a := by
  let U := upperRootMatrixGroup (K := K) a
  let T : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    suzukiTorusOperatorGroup (K := K) a
  let B := suzukiPointStabilizerOperatorGroup (K := K) a
  let w := suzukiWeylOperator (K := K)
  let d := suzukiTorusOperator a l
  have hdT : d ∈ T := by
    change (suzukiTorusOperator (K := K) a l) ∈
      suzukiTorusOperatorGroup (K := K) a
    exact suzukiTorusOperator_mem_torusOperatorGroup (K := K) a l
  have hdiT : d⁻¹ ∈ T := T.inv_mem hdT
  have hdB : d ∈ B :=
    suzukiTorusOperatorGroup_le_suzukiPointStabilizerOperatorGroup (K := K) a hdT
  have hdiB : d⁻¹ ∈ B :=
    suzukiTorusOperatorGroup_le_suzukiPointStabilizerOperatorGroup (K := K) a hdiT
  have hww : w * w = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w, suzukiWeylOperator, suzukiWeylMatrix,
        Matrix.mul_apply, Fin.sum_univ_four]
  have hwd : w * d * w = d⁻¹ := by
    simpa [w, d, suzukiTorusOperator_inv] using
      suzukiWeylOperator_conj_torus (K := K) a l
  have hwd' : w * d = d⁻¹ * w := by
    calc
      w * d = w * d * 1 := by simp
      _ = w * d * (w * w) := by rw [hww]
      _ = (w * d * w) * w := by group
      _ = d⁻¹ * w := by rw [hwd]
  rcases hg with hg | ⟨b, hb, y, hy, rfl⟩
  · exact Or.inl (mul_mem hg hdB)
  · have hnorm := suzukiTorusOperator_mem_normalizer_upperRoot
      (K := K) a hK pi hpi_sq hpi_formula l⁻¹
    have hy' : d⁻¹ * y * d ∈ U := by
      have hforward := (Subgroup.mem_set_normalizer_iff.mp hnorm) y
      have hconj := hforward.mp hy
      simpa [d, suzukiTorusOperator_inv] using hconj
    right
    refine ⟨b * d⁻¹, mul_mem hb hdiB, d⁻¹ * y * d, hy', ?_⟩
    change (b * w * y) * d = (b * d⁻¹) * w * (d⁻¹ * y * d)
    calc
      (b * w * y) * d = b * w * (y * d) := by group
      _ = b * w * (d * (d⁻¹ * y * d)) := by rw [show y * d = d * (d⁻¹ * y * d) by group]
      _ = b * (w * d) * (d⁻¹ * y * d) := by group
      _ = b * (d⁻¹ * w) * (d⁻¹ * y * d) := by rw [hwd']
      _ = (b * d⁻¹) * w * (d⁻¹ * y * d) := by group

/-- Right multiplication by the Weyl operator preserves the union of the
Borel cell and the big Bruhat cell. In the big-cell case, the nonzero
Weyl–root factorization rewrites `w * U * w` back into `B * w * U`. -/
theorem mul_mem_suzukiBorelOrBigCell_of_weyl [Finite K]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : Matrix.GeneralLinearGroup (Fin 4) K}
    (hg : g ∈ (suzukiPointStabilizerOperatorGroup (K := K) a : Set _) ∪
      suzukiBigCellOperatorGroup (K := K) a) :
    g * suzukiWeylOperator (K := K) ∈
      (suzukiPointStabilizerOperatorGroup (K := K) a : Set _) ∪
        suzukiBigCellOperatorGroup (K := K) a := by
  let w := suzukiWeylOperator (K := K)
  have hww : w * w = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w, suzukiWeylOperator, suzukiWeylMatrix,
        Matrix.mul_apply, Fin.sum_univ_four]
  rcases hg with hg | ⟨b, hb, y, hy, rfl⟩
  · right
    refine ⟨g, hg, 1, one_mem _, ?_⟩
    simp [w]
  · have hyset : y ∈ (upperRootMatrixGroup (K := K) a :
        Set (Matrix.GeneralLinearGroup (Fin 4) K)) := hy
    rw [upperRootMatrixGroup_eq_paramRange (K := K) a hK] at hyset
    obtain ⟨c, d, rfl⟩ := hyset
    by_cases hzero : (c, d) = (0, 0)
    · have hc : c = 0 := congrArg Prod.fst hzero
      have hd : d = 0 := congrArg Prod.snd hzero
      left
      have hroot : upperRootOperator a c d = 1 := by
        rw [hc, hd]
        change suzukiSGL a (0 : K) 0 = 1
        exact suzukiSGL_zero_zero (a := a) (K := K)
      rw [hroot, mul_one, mul_assoc, hww, mul_one]
      exact hb
    · obtain ⟨x, y, l, c', d', hfactor⟩ :=
        exists_suzukiWeyl_upperRoot_weyl_factorization (K := K) a hK c d hzero
      have hrootB : upperRootOperator a x y ∈
          suzukiPointStabilizerOperatorGroup (K := K) a :=
        upperRootMatrixGroup_le_suzukiPointStabilizerOperatorGroup (K := K) a (by
          change upperRootOperator a x y ∈
            (upperRootMatrixGroup (K := K) a : Set _)
          rw [upperRootMatrixGroup_eq_paramRange (K := K) a hK]
          exact ⟨x, y, rfl⟩)
      have hrootU : upperRootOperator a c' d' ∈ upperRootMatrixGroup (K := K) a := by
        change upperRootOperator a c' d' ∈
          (upperRootMatrixGroup (K := K) a : Set _)
        rw [upperRootMatrixGroup_eq_paramRange (K := K) a hK]
        exact ⟨c', d', rfl⟩
      let D := suzukiTorusOperator a l
      have hwd : suzukiWeylOperator (K := K) * D * suzukiWeylOperator (K := K) = D⁻¹ := by
        simpa [D, suzukiTorusOperator_inv] using
          suzukiWeylOperator_conj_torus (K := K) a l
      have hwd' : suzukiWeylOperator (K := K) * D = D⁻¹ *
          suzukiWeylOperator (K := K) := by
        calc
          suzukiWeylOperator * D = suzukiWeylOperator * D * 1 := by simp
          _ = suzukiWeylOperator * D *
              (suzukiWeylOperator * suzukiWeylOperator) := by rw [hww]
          _ = (suzukiWeylOperator * D * suzukiWeylOperator) *
              suzukiWeylOperator := by group
          _ = D⁻¹ * suzukiWeylOperator := by rw [hwd]
      right
      refine ⟨b * (upperRootOperator a x y * D⁻¹),
        mul_mem hb (mul_mem hrootB
          (suzukiTorusOperatorGroup_le_suzukiPointStabilizerOperatorGroup
            (K := K) a
            ((suzukiTorusOperatorGroup (K := K) a).inv_mem
              (suzukiTorusOperator_mem_torusOperatorGroup (K := K) a l)))),
        upperRootOperator a c' d', hrootU, ?_⟩
      calc
        (b * suzukiWeylOperator) * upperRootOperator a c d * suzukiWeylOperator =
            b * (suzukiWeylOperator * upperRootOperator a c d * suzukiWeylOperator) := by
              group
        _ = b * (upperRootOperator a x y * suzukiWeylOperator *
              D * upperRootOperator a c' d') := by rw [hfactor]
        _ = b * (upperRootOperator a x y * (suzukiWeylOperator * D)) *
              upperRootOperator a c' d' := by group
        _ = b * (upperRootOperator a x y * (D⁻¹ * suzukiWeylOperator)) *
              upperRootOperator a c' d' := by rw [hwd']
        _ = (b * (upperRootOperator a x y * D⁻¹)) *
              suzukiWeylOperator * upperRootOperator a c' d' := by group

/-- Every element of the generated Suzuki operator group lies in the local
Borel cell or its big Bruhat cell. This closes the generator-stability
induction using the actual upper-root, torus, and Weyl generators. -/
theorem suzukiUpperMatrixGroup_mem_borelOrBigCell [Finite K]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    (g : Chevalley.suzukiUpperMatrixGroup a K) :
    (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
      (suzukiPointStabilizerOperatorGroup (K := K) a : Set _) ∪
        suzukiBigCellOperatorGroup (K := K) a := by
  let U := upperRootMatrixGroup (K := K) a
  let B := suzukiPointStabilizerOperatorGroup (K := K) a
  let w := suzukiWeylOperator (K := K)
  let gens := Chevalley.suzukiUpperMatrixGenerators a K
  have hgenClass (x : Matrix.GeneralLinearGroup (Fin 4) K) (hx : x ∈ gens) :
      (∃ u v : K, x = upperRootOperator a u v) ∨
      (∃ l : Kˣ, x = suzukiTorusOperator a l) ∨ x = w := by
    change ((x : Matrix (Fin 4) (Fin 4) K).transpose) ∈
      {M | (∃ u v : K, M = suzukiS a u v) ∨
        (∃ l : Kˣ, M = suzukiD a l) ∨ M = Chevalley.suzukiW K} at hx
    rcases hx with ⟨u, v, hroot⟩ | ⟨l, htorus⟩ | hw
    · left
      refine ⟨u, v, ?_⟩
      apply Units.ext
      apply Matrix.transpose_injective
      simpa [upperRootOperator, suzukiSGL] using hroot
    · right
      left
      refine ⟨l, ?_⟩
      have hmat : (x : Matrix (Fin 4) (Fin 4) K) = suzukiD a l := by
        calc
          (x : Matrix (Fin 4) (Fin 4) K) =
              ((x : Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
          _ = (suzukiD a l).transpose := congrArg Matrix.transpose htorus
          _ = suzukiD a l := by simp [suzukiD]
      apply Units.ext
      simpa [suzukiTorusOperator] using hmat
    · right
      right
      have hmat : (x : Matrix (Fin 4) (Fin 4) K) = Chevalley.suzukiW K := by
        calc
          (x : Matrix (Fin 4) (Fin 4) K) =
              ((x : Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
          _ = (Chevalley.suzukiW K).transpose := congrArg Matrix.transpose hw
          _ = Chevalley.suzukiW K := by
            ext i j
            simp [Chevalley.suzukiW, Nat.add_comm]
      apply Units.ext
      simpa [w, suzukiWeylOperator, suzukiWeylMatrix,
        Chevalley.suzukiW] using hmat
  have hrootMem (u v : K) : upperRootOperator a u v ∈ U := by
    change upperRootOperator a u v ∈
      (upperRootMatrixGroup (K := K) a : Set _)
    rw [upperRootMatrixGroup_eq_paramRange (K := K) a hK]
    exact ⟨u, v, rfl⟩
  have hrootInvMem (u v : K) :
      (upperRootOperator a u v)⁻¹ ∈ U := by
    have hinv : (upperRootOperator a u v)⁻¹ =
        upperRootOperator a u (v + u ^ (2 ^ (a + 1) + 1)) := by
      change (suzukiSGL a u v)⁻¹ =
        suzukiSGL a u (v + u ^ (2 ^ (a + 1) + 1))
      exact suzukiSGL_inv a hK u v
    rw [hinv]
    exact hrootMem u (v + u ^ (2 ^ (a + 1) + 1))
  have hw_sq : w * w = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w, suzukiWeylOperator, suzukiWeylMatrix,
        Matrix.mul_apply, Fin.sum_univ_four]
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw_sq
  have hclosure : ∀ x : Matrix.GeneralLinearGroup (Fin 4) K,
      x ∈ Chevalley.suzukiUpperMatrixGroup a K →
      x ∈ (B : Set _) ∪ suzukiBigCellOperatorGroup (K := K) a := by
    intro x hx
    refine Subgroup.closure_induction_right
      (p := fun x _ => x ∈ (B : Set _) ∪ suzukiBigCellOperatorGroup (K := K) a)
      (Or.inl (one_mem B)) ?_ ?_ hx
    · intro x hx y hy ih
      rcases hgenClass y hy with hroot | htorus | hw
      · rcases hroot with ⟨u, v, rfl⟩
        exact mul_mem_suzukiBorelOrBigCell_of_upperRoot ih (hrootMem u v)
      · rcases htorus with ⟨l, rfl⟩
        exact mul_mem_suzukiBorelOrBigCell_of_torus (K := K) a hK pi
          hpi_sq hpi_formula ih l
      · rw [hw]
        exact mul_mem_suzukiBorelOrBigCell_of_weyl (K := K) a hK ih
    · intro x hx y hy ih
      rcases hgenClass y hy with hroot | htorus | hw
      · rcases hroot with ⟨u, v, rfl⟩
        exact mul_mem_suzukiBorelOrBigCell_of_upperRoot ih
          (hrootInvMem u v)
      · rcases htorus with ⟨l, rfl⟩
        rw [suzukiTorusOperator_inv]
        exact mul_mem_suzukiBorelOrBigCell_of_torus (K := K) a hK pi
          hpi_sq hpi_formula ih l⁻¹
      · rw [hw, hw_inv]
        exact mul_mem_suzukiBorelOrBigCell_of_weyl (K := K) a hK ih
  exact hclosure g.1 g.2

/-- No element in the local big Bruhat cell fixes the ovoid point at
infinity. The left Borel factor fixes infinity and the right root factor
fixes it, so such a fixed point would force the Weyl operator to fix infinity,
contrary to its explicit action into the finite chart. -/
theorem suzukiBigCellOperatorGroup_not_fixes_infinity
    (a : ℕ) (pi : K ≃+* K)
    {g : Matrix.GeneralLinearGroup (Fin 4) K}
    (hg : g ∈ suzukiBigCellOperatorGroup (K := K) a)
    (hfix : (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidInfinity) : False := by
  rcases hg with ⟨b, hb, y, hy, rfl⟩
  have hbfix : (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidInfinity := by
    have hb' := suzukiPointStabilizerOperatorGroup_le_stabilizer (K := K) a hb
    change Matrix.GeneralLinearGroup.toLin b ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K)) at hb'
    exact MulAction.mem_stabilizer_iff.mp hb'
  have hyfix : (Matrix.GeneralLinearGroup.toLin y).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidInfinity :=
    upperRootMatrixGroup_smul_infinity (K := K) a ⟨y, hy⟩
  have hcomp : (Matrix.GeneralLinearGroup.toLin
      (b * suzukiWeylOperator (K := K) * y)).toLinearEquiv •
        ovoidInfinity (K := K) =
      (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
            (suzukiWeylOperator (K := K))).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin y).toLinearEquiv •
            ovoidInfinity (K := K))) := by
    change (Matrix.GeneralLinearGroup.toLin
        ((b * suzukiWeylOperator (K := K)) * y)).toLinearEquiv • _ = _
    simp only [(Matrix.GeneralLinearGroup.toLin).map_mul,
      LinearMap.GeneralLinearGroup.toLinearEquiv_mul, mul_smul]
  have hwfix : (Matrix.GeneralLinearGroup.toLin
      (suzukiWeylOperator (K := K))).toLinearEquiv •
        ovoidInfinity (K := K) = ovoidInfinity := by
    have hbw : (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
            (suzukiWeylOperator (K := K))).toLinearEquiv •
          ovoidInfinity (K := K)) = ovoidInfinity := by
      calc
        (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
            ((Matrix.GeneralLinearGroup.toLin
                (suzukiWeylOperator (K := K))).toLinearEquiv •
              ovoidInfinity (K := K)) =
            (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
              ((Matrix.GeneralLinearGroup.toLin
                  (suzukiWeylOperator (K := K))).toLinearEquiv •
                ((Matrix.GeneralLinearGroup.toLin y).toLinearEquiv •
                  ovoidInfinity (K := K))) := by rw [hyfix]
        _ = (Matrix.GeneralLinearGroup.toLin
              (b * suzukiWeylOperator (K := K) * y)).toLinearEquiv •
              ovoidInfinity (K := K) := hcomp.symm
        _ = ovoidInfinity (K := K) := hfix
    apply smul_left_cancel (Matrix.GeneralLinearGroup.toLin b)
    calc
      (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin
              (suzukiWeylOperator (K := K))).toLinearEquiv •
            ovoidInfinity (K := K)) = ovoidInfinity := hbw
      _ = (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
          ovoidInfinity (K := K) := hbfix.symm
  have hne : ovoidPoint pi 0 0 ≠ ovoidInfinity (K := K) := by
    intro heq
    exact ovoidInfinity_not_mem_range pi ⟨(0, 0), heq⟩
  rw [suzukiWeylOperator_smul_infinity pi] at hwfix
  exact hne hwfix

/-- In the actual generated Suzuki operator group, fixing infinity is
equivalent to belonging to the local root–torus subgroup. This is the local
point-stabilizer recognition interface used by the external simplicity
argument. -/
theorem suzukiUpperMatrixGroup_mem_pointStabilizer_iff
    [Finite K] (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    (g : Chevalley.suzukiUpperMatrixGroup a K) :
    (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
        (suzukiPointStabilizerOperatorGroup (K := K) a : Set _) ↔
      (Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity (K := K) = ovoidInfinity := by
  constructor
  · intro hg
    have hst := suzukiPointStabilizerOperatorGroup_le_stabilizer (K := K) a hg
    change Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K)) at hst
    exact MulAction.mem_stabilizer_iff.mp hst
  · intro hfix
    rcases suzukiUpperMatrixGroup_mem_borelOrBigCell
        (K := K) a hK pi hpi_sq hpi_formula g with hB | hbig
    · exact hB
    · exact (suzukiBigCellOperatorGroup_not_fixes_infinity
        (K := K) a pi hbig hfix).elim

end InfoGeometry.Exceptional.CFSGPort.Suzuki
