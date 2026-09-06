import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
# InfoGeometry.Modular.PSL2Z

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
[det2_neg, det2_mul, SL2Z neg/mul closure, R_refl, R_symm, R_trans,
 PSL2Z_setoid, mul_compat, PSL2Z_mul, PSL2Z_mk_neg_eq_mk]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
[None.]

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
[This file constructs the quotient type and multiplication descent for PSL(2,Z).
 It does not prove the full group structure on PSL2Z.
 It does not prove a modular action on the upper half-plane.
 It does not prove a U-duality theorem.]
-/

namespace InfoGeometry.Modular.PSL2Z

open Matrix

abbrev M2Z : Type :=
  Matrix (Fin 2) (Fin 2) ℤ

def det2 (M : M2Z) : ℤ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

theorem det2_neg (A : M2Z) :
    det2 (-A) = det2 A := by
  unfold det2
  simp

theorem det2_mul (A B : M2Z) :
    det2 (A * B) = det2 A * det2 B := by
  unfold det2
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

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

def PSL2Z_setoid : Setoid SL2Z where
  r := R
  iseqv := ⟨R_refl, @R_symm, @R_trans⟩

def PSL2Z : Type :=
  Quotient PSL2Z_setoid

def PSL2Z_mk (A : SL2Z) : PSL2Z :=
  Quotient.mk PSL2Z_setoid A

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

def PSL2Z_mul : PSL2Z → PSL2Z → PSL2Z :=
  Quotient.map₂
    (fun A B : SL2Z => A * B)
    (by
      intro A₁ A₂ hA B₁ B₂ hB
      exact mul_compat hA hB)

instance : Mul PSL2Z where
  mul := PSL2Z_mul

@[simp]
theorem PSL2Z_mul_mk (A B : SL2Z) :
    PSL2Z_mk (A * B) = PSL2Z_mk A * PSL2Z_mk B := by
  rfl

theorem PSL2Z_mk_neg_eq_mk (A : SL2Z) :
    PSL2Z_mk (-A) = PSL2Z_mk A := by
  exact Quotient.sound (Or.inr rfl)

end InfoGeometry.Modular.PSL2Z
