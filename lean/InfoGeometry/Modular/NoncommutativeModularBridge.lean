import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Modular.Noncommutative

variable {A : Type*} [Ring A]

def adK (K X : A) : A := K * X - X * K

@[simp] theorem adK_apply (K X : A) : adK K X = K * X - X * K := rfl

theorem adK_add (K X Y : A) :
    adK K (X + Y) = adK K X + adK K Y := by
  dsimp [adK]
  simp only [mul_add, add_mul]
  abel

theorem adK_mul (K X Y : A) :
    adK K (X * Y) = adK K X * Y + X * adK K Y := by
  dsimp [adK]
  simp only [mul_assoc, sub_mul, mul_sub]
  abel

@[simp] theorem adK_one (K : A) : adK K 1 = 0 := by simp [adK]

def IsDerivation (D : A →ₗ[ℤ] A) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

structure NCDerivation (A : Type*) [Ring A] where
  toLinearMap : A →ₗ[ℤ] A
  leibniz' : IsDerivation toLinearMap

instance : CoeFun (NCDerivation A) (fun _ => A → A) where
  coe D := D.toLinearMap

theorem NCDerivation.leibniz (D : NCDerivation A) (x y : A) :
    D (x * y) = D x * y + x * D y := D.leibniz' x y

theorem derivation_one (D : A →ₗ[ℤ] A) (hD : IsDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  have h' : D 1 = D 1 + D 1 := by simpa only [mul_one, one_mul] using h
  have h'' : D 1 + 0 = D 1 + D 1 := by simpa using h'
  exact (add_left_cancel h'').symm

@[simp] theorem NCDerivation.map_one (D : NCDerivation A) : D 1 = 0 :=
  derivation_one D.toLinearMap D.leibniz'

@[ext] theorem NCDerivation.ext {D E : NCDerivation A}
    (h : ∀ X, D X = E X) : D = E := by
  cases D with
  | mk D hD =>
    cases E with
    | mk E hE =>
      have hDE : D = E := by
        ext X
        exact h X
      cases hDE
      rfl

def adKLinear (K : A) : A →ₗ[ℤ] A where
  toFun X := adK K X
  map_add' X Y := adK_add K X Y
  map_smul' n X := by
    change K * (n • X) - (n • X) * K = n • (K * X - X * K)
    have hL : K * (n • X) = n • (K * X) :=
      (AddMonoidHom.mulLeft K).map_zsmul X n
    have hR : (n • X) * K = n • (X * K) :=
      (AddMonoidHom.mulRight K).map_zsmul X n
    rw [hL, hR, smul_sub]

def innerNCDerivation (K : A) : NCDerivation A where
  toLinearMap := adKLinear K
  leibniz' := adK_mul K

def ncDerivationCommutator (D E : NCDerivation A) : NCDerivation A where
  toLinearMap :=
    { toFun := fun X => D (E X) - E (D X)
      map_add' := by
        intro X Y
        simp only [map_add]
        abel
      map_smul' := by
        intro n X
        simp only [map_smul, RingHom.id_apply]
        simp [smul_sub] }
  leibniz' := by
    intro X Y
    change D (E (X * Y)) - E (D (X * Y)) =
      (D (E X) - E (D X)) * Y + X * (D (E Y) - E (D Y))
    rw [E.leibniz, D.leibniz, D.toLinearMap.map_add,
      E.toLinearMap.map_add, D.leibniz, D.leibniz,
      E.leibniz, E.leibniz]
    simp only [sub_mul, mul_sub]
    abel

theorem ncDerivationCommutator_apply (D E : NCDerivation A) (X : A) :
    ncDerivationCommutator D E X = D (E X) - E (D X) := rfl

theorem ncDerivationCommutator_skew (D E : NCDerivation A) (X : A) :
    ncDerivationCommutator D E X = -ncDerivationCommutator E D X := by
  simp only [ncDerivationCommutator_apply]
  abel

@[simp] theorem ncDerivationCommutator_self (D : NCDerivation A) (X : A) :
    ncDerivationCommutator D D X = 0 := by
  simp only [ncDerivationCommutator_apply]
  abel

theorem ncDerivationCommutator_jacobi
    (D E F : NCDerivation A) (X : A) :
    ncDerivationCommutator D (ncDerivationCommutator E F) X +
        ncDerivationCommutator E (ncDerivationCommutator F D) X +
        ncDerivationCommutator F (ncDerivationCommutator D E) X = 0 := by
  simp only [ncDerivationCommutator_apply, map_sub]
  abel

theorem ncDerivationCommutator_inner_apply
    (D : NCDerivation A) (K X : A) :
    ncDerivationCommutator D (innerNCDerivation K) X =
      innerNCDerivation (D K) X := by
  change D (adK K X) - adK K (D X) = adK (D K) X
  dsimp [adK]
  rw [D.toLinearMap.map_sub, D.leibniz, D.leibniz]
  abel

theorem ncDerivationCommutator_inner
    (D : NCDerivation A) (K : A) :
    ncDerivationCommutator D (innerNCDerivation K) =
      innerNCDerivation (D K) := by
  apply NCDerivation.ext
  intro X
  exact ncDerivationCommutator_inner_apply D K X

theorem innerNCDerivation_bracket (K₁ K₂ : A) :
    ncDerivationCommutator (innerNCDerivation K₁) (innerNCDerivation K₂) =
      innerNCDerivation (adK K₁ K₂) := by
  apply NCDerivation.ext
  intro X
  exact ncDerivationCommutator_inner_apply (innerNCDerivation K₁) K₂ X

def dlog (D : A →ₗ[ℤ] A) (u : Aˣ) : A :=
  (↑(u⁻¹) : A) * D (u : A)

theorem dlog_eq_zero_of_fixed (D : A →ₗ[ℤ] A) (u : Aˣ)
    (h : D (u : A) = 0) : dlog D u = 0 := by simp [dlog, h]

@[simp] theorem dlog_one (D : A →ₗ[ℤ] A) (hD : IsDerivation D) :
    dlog D 1 = 0 := by simp [dlog, derivation_one D hD]

theorem dlog_mul (D : A →ₗ[ℤ] A) (hD : IsDerivation D) (u v : Aˣ) :
    dlog D (u * v) =
      (↑(v⁻¹) : A) * dlog D u * (v : A) + dlog D v := by
  unfold dlog
  have hprod : D ((u : A) * (v : A)) =
      D (u : A) * (v : A) + (u : A) * D (v : A) := hD _ _
  change (↑((u * v)⁻¹) : A) * D ((u : A) * (v : A)) = _
  rw [hprod, mul_inv_rev]
  change ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) *
      (D (u : A) * (v : A) + (u : A) * D (v : A)) = _
  have hu : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
  simp only [mul_add, mul_assoc]
  have hterm : (↑(v⁻¹) : A) * ((↑(u⁻¹) : A) *
      ((u : A) * D (v : A))) = (↑(v⁻¹) : A) * D (v : A) := by
    calc
      _ = (↑(v⁻¹) : A) * (((↑(u⁻¹) : A) * (u : A)) * D (v : A)) := by
        rw [mul_assoc]
      _ = _ := by rw [hu, one_mul]
  rw [hterm]

theorem dlog_inv (D : A →ₗ[ℤ] A) (hD : IsDerivation D) (u : Aˣ) :
    dlog D (u⁻¹) = -((u : A) * dlog D u * (↑(u⁻¹) : A)) := by
  unfold dlog
  have hone : D (1 : A) = 0 := derivation_one D hD
  have hprod : D ((u : A) * (↑(u⁻¹) : A)) =
      D (u : A) * (↑(u⁻¹) : A) + (u : A) * D (↑(u⁻¹) : A) := hD _ _
  have hunit : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  rw [hunit, hone] at hprod
  have hinv : (u : A) * D (↑(u⁻¹) : A) =
      -(D (u : A) * (↑(u⁻¹) : A)) := eq_neg_of_add_eq_zero_right hprod.symm
  calc
    (↑((u⁻¹)⁻¹) : A) * D (↑(u⁻¹) : A) =
        (u : A) * D (↑(u⁻¹) : A) := by simp
    _ = _ := hinv
    _ = -((u : A) * ((↑(u⁻¹) : A) * D (u : A)) *
        (↑(u⁻¹) : A)) := by
      have hrewrite : (u : A) * ((↑(u⁻¹) : A) * D (u : A)) *
          (↑(u⁻¹) : A) = D (u : A) * (↑(u⁻¹) : A) := by
        rw [← mul_assoc, hunit, one_mul]
      exact congrArg Neg.neg hrewrite.symm

def NCDerivation.dlog (D : NCDerivation A) (u : Aˣ) : A := dlog D.toLinearMap u

theorem NCDerivation.dlog_mul (D : NCDerivation A) (u v : Aˣ) :
    D.dlog (u * v) = (↑(v⁻¹) : A) * D.dlog u * (v : A) + D.dlog v :=
  dlog_mul D.toLinearMap D.leibniz' u v

theorem NCDerivation.dlog_inv (D : NCDerivation A) (u : Aˣ) :
    D.dlog (u⁻¹) = -((u : A) * D.dlog u * (↑(u⁻¹) : A)) :=
  dlog_inv D.toLinearMap D.leibniz' u

end InfoGeometry.Modular.Noncommutative

end noncomputable section
