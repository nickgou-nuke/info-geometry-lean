/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Int.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

set_option autoImplicit false

/-!
# InfoGeometry.Modular.PSL2Z

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
[det2_neg, det2_mul, SL2Z neg/mul closure, R_refl, R_symm, R_trans,
 projectiveSetoid, mul_compat, mul, mk_neg_eq_mk, SL2Z inverse,
 quotient group structure]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
[None.]

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
[This file constructs the quotient type and full group structure for PSL(2,Z).
 It does not prove a modular action on the upper half-plane.
 It does not prove a U-duality theorem.]
-/

namespace InfoGeometry.Modular.PSL2Z

open Matrix

abbrev M2Z : Type :=
  Matrix (Fin 2) (Fin 2) ℤ

def det2 (M : M2Z) : ℤ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

lemma det2_eq_matrix_det (M : M2Z) :
    det2 M = Matrix.det M := by
  simp [det2, Matrix.det_fin_two]

theorem det2_neg (A : M2Z) :
    det2 (-A) = det2 A := by
  unfold det2
  simp

theorem det2_mul (A B : M2Z) :
    det2 (A * B) = det2 A * det2 B := by
  rw [det2_eq_matrix_det, Matrix.det_mul, ← det2_eq_matrix_det,
    ← det2_eq_matrix_det]

/-! A concrete non-commutativity witness for the ambient matrix carrier. -/
def matrixUnit01 : M2Z :=
  !![0, 1; 0, 0]

def matrixUnit10 : M2Z :=
  !![0, 0; 1, 0]

theorem matrixUnit01_mul_matrixUnit10_ne_matrixUnit10_mul_matrixUnit01 :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have h00 := congrArg (fun M : M2Z => M 0 0) h
  simp [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_two] at h00

abbrev SL2Z : Type :=
  {M : M2Z // det2 M = 1}

namespace SL2Z

@[ext]
theorem ext {A B : SL2Z} (h : A.val = B.val) : A = B :=
  Subtype.ext h

instance : Neg SL2Z where
  neg A :=
    ⟨-A.val, by
      rw [det2_neg]
      exact A.property⟩

@[simp]
theorem val_neg (A : SL2Z) :
    (-A).val = -A.val :=
  rfl

@[simp]
theorem neg_neg (A : SL2Z) :
    -(-A) = A := by
  apply ext
  simp

instance : Mul SL2Z where
  mul A B :=
    ⟨A.val * B.val, by
      rw [det2_mul, A.property, B.property]
      norm_num⟩

@[simp]
theorem val_mul (A B : SL2Z) :
    (A * B).val = A.val * B.val :=
  rfl

theorem mul_neg (A B : SL2Z) :
    A * (-B) = -(A * B) := by
  apply ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_mul (A B : SL2Z) :
    (-A) * B = -(A * B) := by
  apply ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_mul_neg (A B : SL2Z) :
    (-A) * (-B) = A * B := by
  calc
    (-A) * (-B) = -(A * (-B)) := by
      exact neg_mul A (-B)
    _ = -(-(A * B)) := by
      rw [mul_neg]
    _ = A * B := by
      simp

instance : One SL2Z where
  one :=
    ⟨1, by
      exact (det2_eq_matrix_det (1 : M2Z)).trans Matrix.det_one⟩

@[simp]
theorem val_one : (1 : SL2Z).val = 1 :=
  rfl

instance : Inv SL2Z where
  inv A :=
    ⟨A.val.adjugate, by
      rw [det2_eq_matrix_det, Matrix.det_adjugate,
        ← det2_eq_matrix_det, A.property]
      norm_num⟩

@[simp]
theorem val_inv (A : SL2Z) : (A⁻¹).val = A.val.adjugate :=
  rfl

lemma adjugate_neg (A : SL2Z) :
    (-A.val).adjugate = -(A.val.adjugate) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two]

theorem inv_mul (A : SL2Z) : A⁻¹ * A = 1 := by
  apply ext
  change A.val.adjugate * A.val = (1 : M2Z)
  rw [Matrix.adjugate_mul, ← det2_eq_matrix_det, A.property]
  simp

theorem mul_inv (A : SL2Z) : A * A⁻¹ = 1 := by
  apply ext
  change A.val * A.val.adjugate = (1 : M2Z)
  rw [Matrix.mul_adjugate, ← det2_eq_matrix_det, A.property]
  simp

end SL2Z

def R (A B : SL2Z) : Prop :=
  A = B ∨ A = -B

lemma R_refl (A : SL2Z) :
    R A A := by
  left
  rfl

lemma R_symm {A B : SL2Z} (h : R A B) :
    R B A := by
  unfold R at h ⊢
  rcases h with rfl | h
  · left
    rfl
  · right
    rw [h]
    simp

lemma R_trans {A B C : SL2Z} (hAB : R A B) (hBC : R B C) :
    R A C := by
  unfold R at hAB hBC ⊢
  rcases hAB with rfl | hAB
  · exact hBC
  · rcases hBC with rfl | hBC
    · right
      exact hAB
    · left
      rw [hAB, hBC]
      simp

def projectiveSetoid : Setoid SL2Z where
  r := R
  iseqv := ⟨R_refl, @R_symm, @R_trans⟩

def Carrier : Type :=
  Quotient projectiveSetoid

def mk (A : SL2Z) : Carrier :=
  Quotient.mk projectiveSetoid A

lemma mul_compat {A₁ A₂ B₁ B₂ : SL2Z}
    (hA : R A₁ A₂) (hB : R B₁ B₂) :
    R (A₁ * B₁) (A₂ * B₂) := by
  unfold R at hA hB ⊢
  rcases hA with rfl | hA <;> rcases hB with rfl | hB
  · left
    rfl
  · right
    rw [hB]
    exact SL2Z.mul_neg A₁ B₂
  · right
    rw [hA]
    exact SL2Z.neg_mul A₂ B₁
  · left
    rw [hA, hB]
    exact SL2Z.neg_mul_neg A₂ B₂

def mul : Carrier → Carrier → Carrier :=
  Quotient.map₂
    (fun A B : SL2Z => A * B)
    (by
      intro A₁ A₂ hA B₁ B₂ hB
      exact mul_compat hA hB)

instance : Mul Carrier where
  mul := mul

@[simp]
theorem mul_mk (A B : SL2Z) :
    mk (A * B) = mk A * mk B := by
  rfl

theorem mk_neg_eq_mk (A : SL2Z) :
    mk (-A) = mk A := by
  exact Quotient.sound (Or.inr rfl)

private lemma inv_compat {A B : SL2Z} (h : R A B) :
    R A⁻¹ B⁻¹ := by
  unfold R at h ⊢
  rcases h with rfl | h
  · left
    rfl
  · right
    rw [h]
    apply SL2Z.ext
    change (-B.val).adjugate = -(B.val.adjugate)
    exact SL2Z.adjugate_neg B

def inv : Carrier → Carrier :=
  Quotient.map
    (fun A : SL2Z => A⁻¹)
    (by
      intro A B h
      exact inv_compat h)

instance : Inv Carrier where
  inv := inv

@[simp]
theorem inv_mk (A : SL2Z) : inv (mk A) = mk A⁻¹ := by
  rfl

instance : One Carrier where
  one := mk 1

@[simp]
theorem one_eq_mk : (1 : Carrier) = mk 1 :=
  rfl

theorem mul_assoc_carrier (a b c : Carrier) :
    (a * b) * c = a * (b * c) := by
  refine Quotient.inductionOn a ?_
  intro A
  refine Quotient.inductionOn b ?_
  intro B
  refine Quotient.inductionOn c ?_
  intro C
  change mk ((A * B) * C) = mk (A * (B * C))
  congr 1
  apply SL2Z.ext
  simp [Matrix.mul_assoc]

theorem one_mul_carrier (a : Carrier) :
    (1 : Carrier) * a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  change mk (1 * A) = mk A
  congr 1
  apply SL2Z.ext
  simp

theorem mul_one_carrier (a : Carrier) :
    a * (1 : Carrier) = a := by
  refine Quotient.inductionOn a ?_
  intro A
  change mk (A * 1) = mk A
  congr 1
  apply SL2Z.ext
  simp

theorem inv_mul_cancel_carrier (a : Carrier) :
    a⁻¹ * a = (1 : Carrier) := by
  refine Quotient.inductionOn a ?_
  intro A
  change mk (A⁻¹ * A) = mk 1
  rw [SL2Z.inv_mul]

instance : Group Carrier where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc := mul_assoc_carrier
  one_mul := one_mul_carrier
  mul_one := mul_one_carrier
  inv_mul_cancel := inv_mul_cancel_carrier

end InfoGeometry.Modular.PSL2Z
