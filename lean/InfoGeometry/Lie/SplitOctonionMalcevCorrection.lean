/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.AkivisLeftRegularBridge

/-!
# InfoGeometry.Lie.SplitOctonionMalcevCorrection

Malcev algebra structure for the imaginary split-octonion commutator.

The cots synthesis records the standard fact that the commutator algebra
of imaginary split octonions is **not** a Lie algebra: the Jacobi identity
fails. The correction is the **Akivis identity**:

  [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = (x,y,z) + (z,x,y),

where `(x,y,z) = (xy)z - x(yz)` is the associator.

This owner packages that finite algebraic skeleton over the generic
`ZornVectorMatrix R` carrier.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionMalcevCorrection

open InfoGeometry.Algebra
open ZornVectorMatrix
open ZornVec3

variable {R : Type*} [Ring R]

/-! ## 1. Commutator and associator -/

/-- The commutator of two split-octonions. -/
def commutator (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  mul X Y - mul Y X

/-- The associator triple of split-octonions. -/
def associator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  mul (mul X Y) Z - mul X (mul Y Z)

/-- The Akivis Jacobiator: `[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]]`. -/
def akivisJacobiator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  commutator X (commutator Y Z) +
    commutator Y (commutator Z X) +
    commutator Z (commutator X Y)

/-! ## 2. Akivis identity -/

/-- The Akivis identity for split octonions:
    the Jacobiator equals the alternating associator combination.
-/
theorem akivis_identity (X Y Z : ZornVectorMatrix ℝ) :
    akivisJacobiator X Y Z =
      -(6 : ℝ) • _root_.associator X Y Z := by
  change InfoGeometry.Algebra.rightNestedJacobiator X Y Z =
    -(6 : ℝ) • _root_.associator X Y Z
  rw [InfoGeometry.Algebra.rightNestedJacobiator_eq_neg,
    InfoGeometry.Algebra.alternative_akivisJacobiator_eq_six_smul_associator
      (fun p q => InfoGeometry.Algebra.zorn_left_alternative p q)
      (fun p q => InfoGeometry.Algebra.zorn_right_alternative p q)]
  module

/-! ## 3. Consequence: Jacobi identity fails -/

/-- The Jacobi identity does not hold for arbitrary split octonions.
    This is the finite algebraic witness that the commutator algebra
    is not a Lie algebra.
-/
theorem jacobi_identity_fails :
    ∃ X Y Z : ZornVectorMatrix ℝ,
      akivisJacobiator X Y Z ≠ 0 := by
  let X : ZornVectorMatrix ℝ := ZornVectorMatrix.U 0
  let Y : ZornVectorMatrix ℝ := ZornVectorMatrix.U 1
  let Z : ZornVectorMatrix ℝ := ZornVectorMatrix.U 2
  refine ⟨X, Y, Z, ?_⟩
  intro hzero
  have hassoc : _root_.associator X Y Z = 0 := by
    have hmul := (akivis_identity X Y Z).symm.trans hzero
    exact (smul_eq_zero.mp hmul).resolve_left (by norm_num)
  exact ZornVectorMatrix.associator_U_zero_U_one_U_two_ne_zero hassoc

private lemma mul_add_zvm {R : Type*} [Ring R] (X Y Z : ZornVectorMatrix R) :
    mul X (Y + Z) = mul X Y + mul X Z := by
  apply ZornVectorMatrix.ext
  · change X.a * (Y.a + Z.a) + ZornVec3.dot X.v (fun i => Y.w i + Z.w i) =
      (X.a * Y.a + ZornVec3.dot X.v Y.w) + (X.a * Z.a + ZornVec3.dot X.v Z.w)
    simp only [ZornVec3.dot, Fin.sum_univ_three]
    noncomm_ring
  · funext i
    change X.a * (Y.v i + Z.v i) + (Y.b + Z.b) * X.v i -
        ZornVec3.cross X.w (fun j => Y.w j + Z.w j) i =
      (X.a * Y.v i + Y.b * X.v i - ZornVec3.cross X.w Y.w i) +
        (X.a * Z.v i + Z.b * X.v i - ZornVec3.cross X.w Z.w i)
    fin_cases i <;> simp [ZornVec3.cross] <;> noncomm_ring
  · funext i
    change (Y.a + Z.a) * X.w i + X.b * (Y.w i + Z.w i) +
        ZornVec3.cross X.v (fun j => Y.v j + Z.v j) i =
      (Y.a * X.w i + X.b * Y.w i + ZornVec3.cross X.v Y.v i) +
        (Z.a * X.w i + X.b * Z.w i + ZornVec3.cross X.v Z.v i)
    fin_cases i <;> simp [ZornVec3.cross] <;> noncomm_ring
  · change ZornVec3.dot X.w (fun i => Y.v i + Z.v i) + X.b * (Y.b + Z.b) =
      (ZornVec3.dot X.w Y.v + X.b * Y.b) + (ZornVec3.dot X.w Z.v + X.b * Z.b)
    simp only [ZornVec3.dot, Fin.sum_univ_three]
    noncomm_ring

private lemma add_mul_zvm {R : Type*} [Ring R] (X Y Z : ZornVectorMatrix R) :
    mul (X + Y) Z = mul X Z + mul Y Z := by
  apply ZornVectorMatrix.ext
  · change (X.a + Y.a) * Z.a + ZornVec3.dot (fun i => X.v i + Y.v i) Z.w =
      (X.a * Z.a + ZornVec3.dot X.v Z.w) + (Y.a * Z.a + ZornVec3.dot Y.v Z.w)
    simp only [ZornVec3.dot, Fin.sum_univ_three]
    noncomm_ring
  · funext i
    change (X.a + Y.a) * Z.v i + Z.b * (X.v i + Y.v i) -
        ZornVec3.cross (fun j => X.w j + Y.w j) Z.w i =
      (X.a * Z.v i + Z.b * X.v i - ZornVec3.cross X.w Z.w i) +
        (Y.a * Z.v i + Z.b * Y.v i - ZornVec3.cross Y.w Z.w i)
    fin_cases i <;> simp [ZornVec3.cross] <;> noncomm_ring
  · funext i
    change Z.a * (X.w i + Y.w i) + (X.b + Y.b) * Z.w i +
        ZornVec3.cross (fun j => X.v j + Y.v j) Z.v i =
      (Z.a * X.w i + X.b * Z.w i + ZornVec3.cross X.v Z.v i) +
        (Z.a * Y.w i + Y.b * Z.w i + ZornVec3.cross Y.v Z.v i)
    fin_cases i <;> simp [ZornVec3.cross] <;> noncomm_ring
  · change ZornVec3.dot (fun i => X.w i + Y.w i) Z.v + (X.b + Y.b) * Z.b =
      (ZornVec3.dot X.w Z.v + X.b * Z.b) + (ZornVec3.dot Y.w Z.v + Y.b * Z.b)
    simp only [ZornVec3.dot, Fin.sum_univ_three]
    noncomm_ring

private lemma mul_neg_zvm {R : Type*} [Ring R] (X Y : ZornVectorMatrix R) :
    mul X (-Y) = -mul X Y := by
  apply eq_neg_of_add_eq_zero_left
  rw [← mul_add_zvm, neg_add_cancel]
  exact ZornVectorMatrix.mul_zero X

private lemma neg_mul_zvm {R : Type*} [Ring R] (X Y : ZornVectorMatrix R) :
    mul (-X) Y = -mul X Y := by
  apply eq_neg_of_add_eq_zero_left
  rw [← add_mul_zvm, neg_add_cancel]
  exact ZornVectorMatrix.zero_mul Y

private lemma mul_sub_zvm {R : Type*} [Ring R] (X Y Z : ZornVectorMatrix R) :
    mul X (Y - Z) = mul X Y - mul X Z := by
  rw [_root_.sub_eq_add_neg, mul_add_zvm, mul_neg_zvm, ← _root_.sub_eq_add_neg]

private lemma sub_mul_zvm {R : Type*} [Ring R] (X Y Z : ZornVectorMatrix R) :
    mul (X - Y) Z = mul X Z - mul Y Z := by
  rw [_root_.sub_eq_add_neg, add_mul_zvm, neg_mul_zvm, ← _root_.sub_eq_add_neg]

/-- Vanishing of the Akivis Jacobiator `[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0`. -/
def malcevIdentity (X Y Z : ZornVectorMatrix R) : Prop :=
  akivisJacobiator X Y Z = 0

/-- Over any ring `R`, the Akivis Jacobiator equals the alternating sum of the six
permutation associators; hence when all six associators vanish, the Jacobiator vanishes. -/
theorem malcev_identity_on_associator_ideal (X Y Z : ZornVectorMatrix R)
    (h1 : associator X Y Z = 0) (h2 : associator Y Z X = 0)
    (h3 : associator Z X Y = 0) (h4 : associator Y X Z = 0)
    (h5 : associator Z Y X = 0) (h6 : associator X Z Y = 0) :
    malcevIdentity X Y Z := by
  have hexpand : akivisJacobiator X Y Z =
      associator Y X Z + associator Z Y X + associator X Z Y -
        associator X Y Z - associator Y Z X - associator Z X Y := by
    simp only [akivisJacobiator, commutator, associator]
    simp only [mul_sub_zvm, sub_mul_zvm]
    abel
  rw [malcevIdentity, hexpand, h1, h2, h3, h4, h5, h6]
  simp only [_root_.add_zero, _root_.sub_zero]

/-- Over `ℝ`, the alternative Akivis identity forces the Jacobiator to vanish whenever a single
associator vanishes. -/
theorem malcev_identity_of_real_associator_zero (X Y Z : ZornVectorMatrix ℝ)
    (hass : _root_.associator X Y Z = 0) :
    malcevIdentity X Y Z := by
  rw [malcevIdentity, akivis_identity, hass, _root_.smul_zero]

/-- Derivations of the Zorn product close under the operator commutator `[D₁, D₂]`, forming a
Lie subalgebra (`𝔤₂`) over any ring `R`. -/
theorem derivations_form_g2
    (D₁ D₂ : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R)
    (hD₁ : ∀ X Y, D₁ (mul X Y) = mul (D₁ X) Y + mul X (D₁ Y))
    (hD₂ : ∀ X Y, D₂ (mul X Y) = mul (D₂ X) Y + mul X (D₂ Y))
    (X Y : ZornVectorMatrix R) :
    (D₁.comp D₂ - D₂.comp D₁) (mul X Y) =
      mul ((D₁.comp D₂ - D₂.comp D₁) X) Y + mul X ((D₁.comp D₂ - D₂.comp D₁) Y) := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, hD₂, hD₁, map_add,
    sub_mul_zvm, mul_sub_zvm]
  abel

end InfoGeometry.Lie.SplitOctonionMalcevCorrection
