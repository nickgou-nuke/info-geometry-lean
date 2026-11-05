/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.IsotropicCyclotomicGenesis
import InfoGeometry.GrandUnification.ArchetypeDictionary
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Basic.Real.Basic

/-!
# Deforming an ordered square-zero pair

For square-zero elements `u` and `v` in an associative real algebra, the
deformation `u + δ • v` squares to `δ • (u * v + v * u)`. The normalization
`u * v + v * u = 1` is an explicit additional hypothesis. Under it, the
nonzero parameter `t` produces an involution and its two complementary
idempotents through the existing Peirce-projector owner.

The two ordered products are retained throughout. The exact rescaled
projector identities are algebraic inputs for a separate limit argument;
this file does not assert a continuous extension at `t = 0`.
-/

noncomputable section

namespace InfoGeometry.Algebra.SquareZeroPairDeformation

open IsotropicCyclotomicGenesis
open InfoGeometry.GrandUnification.ArchetypeDictionary

variable {A : Type*} [Ring A]

/-- In a nontrivial algebra, the normalization forces a nonzero first arrow. -/
theorem left_ne_zero [Nontrivial A] (u v : A) (hunit : u * v + v * u = 1) :
    u ≠ 0 := by
  intro hu
  simp only [hu, zero_mul, mul_zero, zero_add] at hunit
  exact zero_ne_one hunit

/-- The normalized square-zero arrows cannot commute in a nontrivial algebra. -/
theorem not_commute [Nontrivial A] (u v : A)
    (hu : u * u = 0) (hv : v * v = 0) (hunit : u * v + v * u = 1) :
    ¬ Commute u v := by
  intro hcomm
  have hreg := (normalized_square_zero_pair_is_mutually_regular u v hu hv hunit).1
  apply left_ne_zero u v hunit
  calc
    u = u * v * u := hreg.symm
    _ = u * (u * v) := by rw [mul_assoc, ← hcomm.eq]
    _ = 0 := by rw [← mul_assoc, hu, zero_mul]

variable [Algebra ℝ A]

/-- A signed deformation of the first square-zero generator. -/
def deformation (u v : A) (δ : ℝ) : A := u + δ • v

/-- Normalization of the deformation at the positive parameter `δ = t²`. -/
def normalized (u v : A) (t : ℝ) : A := t⁻¹ • u + t • v

/-- The existing positive Peirce projector applied to the normalized operator. -/
def projectorPlus (u v : A) (t : ℝ) : A :=
  peircePlus (R := ℝ) (normalized u v t)

/-- The existing negative Peirce projector applied to the normalized operator. -/
def projectorMinus (u v : A) (t : ℝ) : A :=
  peirceMinus (R := ℝ) (normalized u v t)

@[simp] theorem deformation_zero (u v : A) : deformation u v 0 = u := by
  simp [deformation]

private theorem smul_square_zero (x : A) (hx : x * x = 0) (c : ℝ) :
    (c • x) * (c • x) = 0 := by
  rw [smul_mul_smul, hx, smul_zero]

/-- Without normalization, the square retains the ordered round-trip sum. -/
theorem deformation_square_eq_smul_round_trips (u v : A)
    (hu : u * u = 0) (hv : v * v = 0) (δ : ℝ) :
    deformation u v δ * deformation u v δ = δ • (u * v + v * u) := by
  calc
    _ = u * (δ • v) + (δ • v) * u :=
      isotropic_sum_square u (δ • v) hu (smul_square_zero v hv δ)
    _ = δ • (u * v + v * u) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_add]

/-- Normalization is exactly what turns the round-trip sum into the unit. -/
theorem deformation_square (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) (δ : ℝ) :
    deformation u v δ * deformation u v δ = δ • (1 : A) := by
  rw [deformation_square_eq_smul_round_trips u v hu hv, hunit]

theorem normalized_square_eq_round_trips (u v : A)
    (hu : u * u = 0) (hv : v * v = 0) {t : ℝ} (ht : t ≠ 0) :
    normalized u v t * normalized u v t = u * v + v * u := by
  have h := isotropic_sum_square (t⁻¹ • u) (t • v)
    (smul_square_zero u hu t⁻¹) (smul_square_zero v hv t)
  simpa only [normalized, isotropicSum, cornerUnit, smul_mul_smul,
    inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, one_smul] using h

/-- The normalized deformation is an involution at every nonzero parameter. -/
theorem normalized_square (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    normalized u v t * normalized u v t = 1 := by
  rw [normalized_square_eq_round_trips u v hu hv ht, hunit]

/-- Rescaling recovers the original deformation; no square-zero law is needed. -/
theorem smul_normalized (u v : A) {t : ℝ} (ht : t ≠ 0) :
    t • normalized u v t = deformation u v (t ^ 2) := by
  simp only [normalized, deformation, smul_add, smul_smul,
    mul_inv_cancel₀ ht, one_smul, pow_two]

/-- The opposite signed combination has square `-1` under the same normalization. -/
theorem normalized_difference_square (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    (t⁻¹ • u - t • v) * (t⁻¹ • u - t • v) = -(1 : A) := by
  have h := isotropic_difference_square (t⁻¹ • u) (t • v)
    (smul_square_zero u hu t⁻¹) (smul_square_zero v hv t)
  simpa only [isotropicDifference, cornerUnit, smul_mul_smul,
    inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, one_smul, hunit] using h

theorem projectorPlus_add_projectorMinus (u v : A) (t : ℝ) :
    projectorPlus u v t + projectorMinus u v t = 1 :=
  peircePlus_add_peirceMinus (R := ℝ) (normalized u v t)

theorem projectorPlus_sub_projectorMinus (u v : A) (t : ℝ) :
    projectorPlus u v t - projectorMinus u v t = normalized u v t :=
  peircePlus_sub_peirceMinus (R := ℝ) (normalized u v t)

theorem projectorPlus_square (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    projectorPlus u v t * projectorPlus u v t = projectorPlus u v t :=
  peircePlus_sq (R := ℝ) (normalized u v t) (normalized_square u v hu hv hunit ht)

theorem projectorMinus_square (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    projectorMinus u v t * projectorMinus u v t = projectorMinus u v t :=
  peirceMinus_sq (R := ℝ) (normalized u v t) (normalized_square u v hu hv hunit ht)

theorem projectorPlus_mul_projectorMinus (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    projectorPlus u v t * projectorMinus u v t = 0 :=
  peircePlus_mul_peirceMinus (R := ℝ) (normalized u v t)
    (normalized_square u v hu hv hunit ht)

theorem projectorMinus_mul_projectorPlus (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    projectorMinus u v t * projectorPlus u v t = 0 :=
  peirceMinus_mul_peircePlus (R := ℝ) (normalized u v t)
    (normalized_square u v hu hv hunit ht)

theorem normalized_mul_projectorPlus (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    normalized u v t * projectorPlus u v t = projectorPlus u v t := by
  change normalized u v t * ((⅟(2 : ℝ)) • (1 + normalized u v t)) =
    (⅟(2 : ℝ)) • (1 + normalized u v t)
  rw [mul_smul_comm, mul_add, mul_one, normalized_square u v hu hv hunit ht,
    add_comm (normalized u v t) 1]

theorem normalized_mul_projectorMinus (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    normalized u v t * projectorMinus u v t = -projectorMinus u v t := by
  change normalized u v t * ((⅟(2 : ℝ)) • (1 - normalized u v t)) =
    -((⅟(2 : ℝ)) • (1 - normalized u v t))
  rw [mul_smul_comm, mul_sub, mul_one, normalized_square u v hu hv hunit ht,
    ← smul_neg, neg_sub]

theorem projectorPlus_mul_normalized (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    projectorPlus u v t * normalized u v t = projectorPlus u v t := by
  change ((⅟(2 : ℝ)) • (1 + normalized u v t)) * normalized u v t =
    (⅟(2 : ℝ)) • (1 + normalized u v t)
  rw [smul_mul_assoc, add_mul, one_mul, normalized_square u v hu hv hunit ht,
    add_comm (normalized u v t) 1]

theorem projectorMinus_mul_normalized (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    projectorMinus u v t * normalized u v t = -projectorMinus u v t := by
  change ((⅟(2 : ℝ)) • (1 - normalized u v t)) * normalized u v t =
    -((⅟(2 : ℝ)) • (1 - normalized u v t))
  rw [smul_mul_assoc, sub_mul, one_mul, normalized_square u v hu hv hunit ht,
    ← smul_neg, neg_sub]

/-- The positive projector satisfies the left eigenoperator equation. -/
theorem deformation_mul_projectorPlus (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    deformation u v (t ^ 2) * projectorPlus u v t = t • projectorPlus u v t := by
  rw [← smul_normalized u v ht, smul_mul_assoc,
    normalized_mul_projectorPlus u v hu hv hunit ht]

/-- The negative projector has the opposite eigenvalue, in the same order. -/
theorem deformation_mul_projectorMinus (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    deformation u v (t ^ 2) * projectorMinus u v t = (-t) • projectorMinus u v t := by
  rw [← smul_normalized u v ht, smul_mul_assoc,
    normalized_mul_projectorMinus u v hu hv hunit ht, smul_neg, neg_smul]

theorem projectorPlus_mul_deformation (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    projectorPlus u v t * deformation u v (t ^ 2) = t • projectorPlus u v t := by
  rw [← smul_normalized u v ht, mul_smul_comm,
    projectorPlus_mul_normalized u v hu hv hunit ht]

theorem projectorMinus_mul_deformation (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) {t : ℝ} (ht : t ≠ 0) :
    projectorMinus u v t * deformation u v (t ^ 2) = (-t) • projectorMinus u v t := by
  rw [← smul_normalized u v ht, mul_smul_comm,
    projectorMinus_mul_normalized u v hu hv hunit ht, smul_neg, neg_smul]

/-- The projector difference reconstructs the deformed operator. -/
theorem deformation_eq_smul_projector_difference (u v : A) {t : ℝ} (ht : t ≠ 0) :
    deformation u v (t ^ 2) = t • (projectorPlus u v t - projectorMinus u v t) := by
  rw [projectorPlus_sub_projectorMinus, smul_normalized u v ht]

/-- The exact rescaled positive projector has constant term `u / 2`. -/
theorem projectorPlus_residue (u v : A) {t : ℝ} (ht : t ≠ 0) :
    t • projectorPlus u v t =
      (1 / 2 : ℝ) • (t • (1 : A) + u + (t ^ 2) • v) := by
  change t • ((⅟(2 : ℝ)) • (1 + normalized u v t)) = _
  rw [invOf_eq_inv, ← one_div, smul_comm t (1 / 2 : ℝ), smul_add,
    smul_normalized u v ht]
  simp only [deformation, add_assoc]

/-- The exact rescaled negative projector has constant term `-u / 2`. -/
theorem projectorMinus_residue (u v : A) {t : ℝ} (ht : t ≠ 0) :
    t • projectorMinus u v t =
      (1 / 2 : ℝ) • (t • (1 : A) - u - (t ^ 2) • v) := by
  change t • ((⅟(2 : ℝ)) • (1 - normalized u v t)) = _
  rw [invOf_eq_inv, ← one_div, smul_comm t (1 / 2 : ℝ), smul_sub,
    smul_normalized u v ht]
  simp only [deformation, sub_add_eq_sub_sub]

end InfoGeometry.Algebra.SquareZeroPairDeformation
