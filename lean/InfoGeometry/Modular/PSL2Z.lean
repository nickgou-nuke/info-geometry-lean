import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option autoImplicit false

/-!
# InfoGeometry.Modular.PSL2Z

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
[det2_neg, det2_mul, SL2Z neg/mul closure, R_refl, R_symm, R_trans,
 projectiveSetoid, mul_compat, mul, mk_neg_eq_mk]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
[None.]

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
[This file constructs the quotient type, multiplication descent, and group
 structure for PSL(2,Z).
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

def one : SL2Z :=
  ⟨1, by
    unfold det2
    norm_num [Matrix.one_apply]⟩

instance : One SL2Z := ⟨one⟩

@[simp]
theorem val_one : (1 : SL2Z).val = 1 :=
  rfl

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

def inv (A : SL2Z) : SL2Z :=
  ⟨!![A.val 1 1, -A.val 0 1; -A.val 1 0, A.val 0 0], by
    have hdet : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
      simpa [det2] using A.property
    simpa [det2, mul_comm] using hdet⟩

instance : Inv SL2Z := ⟨inv⟩

@[simp]
theorem val_inv (A : SL2Z) :
    (A⁻¹).val = !![A.val 1 1, -A.val 0 1; -A.val 1 0, A.val 0 0] :=
  rfl

theorem mul_inv (A : SL2Z) : A * A⁻¹ = 1 := by
  have hdet : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa [det2] using A.property
  apply ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, inv]
    simpa [mul_comm] using hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two, inv]
    <;> ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, inv]
    <;> ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, inv]
    <;> ring
    simpa [mul_comm, add_comm, sub_eq_add_neg] using hdet

theorem inv_mul (A : SL2Z) : A⁻¹ * A = 1 := by
  have hdet : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa [det2] using A.property
  apply ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, inv]
    simpa [mul_comm] using hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two, inv]
    <;> ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, inv]
    <;> ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, inv]
    <;> ring
    simpa [mul_comm, add_comm, sub_eq_add_neg] using hdet

theorem neg_inv (A : SL2Z) : (-A)⁻¹ = -(A⁻¹) := by
  apply ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, inv]

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

instance : One Carrier where
  one := mk (1 : SL2Z)

@[simp]
theorem mk_one : mk (1 : SL2Z) = (1 : Carrier) :=
  rfl

theorem carrier_mul_assoc (A B C : Carrier) :
    (A * B) * C = A * (B * C) := by
  induction A using Quotient.inductionOn with
  | _ A =>
    induction B using Quotient.inductionOn with
    | _ B =>
      induction C using Quotient.inductionOn with
      | _ C =>
        change mk ((A * B) * C) = mk (A * (B * C))
        apply congrArg mk
        apply SL2Z.ext
        exact Matrix.mul_assoc A.val B.val C.val

theorem carrier_one_mul (A : Carrier) :
    (1 : Carrier) * A = A := by
  induction A using Quotient.inductionOn with
  | _ A =>
    change mk ((1 : SL2Z) * A) = mk A
    apply congrArg mk
    apply SL2Z.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SL2Z.one, Matrix.mul_apply, Fin.sum_univ_two]

theorem carrier_mul_one (A : Carrier) :
    A * (1 : Carrier) = A := by
  induction A using Quotient.inductionOn with
  | _ A =>
    change mk (A * (1 : SL2Z)) = mk A
    apply congrArg mk
    apply SL2Z.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SL2Z.one, Matrix.mul_apply, Fin.sum_univ_two]

instance : Monoid Carrier where
  one := 1
  mul := mul
  one_mul := carrier_one_mul
  mul_one := carrier_mul_one
  mul_assoc := carrier_mul_assoc

def inv : Carrier → Carrier :=
  Quotient.lift
    (fun A : SL2Z => mk (A⁻¹))
    (by
      intro A B h
      rcases h with rfl | h
      · rfl
      · subst A
        change mk ((-B)⁻¹) = mk (B⁻¹)
        rw [SL2Z.neg_inv]
        exact mk_neg_eq_mk _)

instance : Inv Carrier := ⟨inv⟩

@[simp]
theorem inv_mk (A : SL2Z) :
    inv (mk A) = mk (A⁻¹) :=
  rfl

theorem carrier_mul_inv (A : Carrier) :
    A * A⁻¹ = (1 : Carrier) := by
  induction A using Quotient.inductionOn with
  | _ A =>
    change mk (A * A⁻¹) = mk (1 : SL2Z)
    rw [SL2Z.mul_inv]

theorem carrier_inv_mul (A : Carrier) :
    A⁻¹ * A = (1 : Carrier) := by
  induction A using Quotient.inductionOn with
  | _ A =>
    change mk (A⁻¹ * A) = mk (1 : SL2Z)
    rw [SL2Z.inv_mul]

instance : Group Carrier where
  one := 1
  mul := mul
  inv := inv
  one_mul := carrier_one_mul
  mul_one := carrier_mul_one
  mul_assoc := carrier_mul_assoc
  inv_mul_cancel := carrier_inv_mul

end InfoGeometry.Modular.PSL2Z
