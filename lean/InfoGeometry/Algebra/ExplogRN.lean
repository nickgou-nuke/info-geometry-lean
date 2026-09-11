import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic

namespace InfoGeometry.Algebra.ExplogRN

variable {A : Type*} [CommRing A]

def IsDerivation (D : A → A) : Prop :=
  (∀ x y, D (x + y) = D x + D y) ∧
  (∀ x y, D (x * y) = D x * y + x * D y)

theorem derivation_one (D : A → A) (hD : IsDerivation D) : D 1 = 0 := by
  have hmul : D 1 = D 1 + D 1 := by
    calc
      D 1 = D (1 * 1) := by rw [mul_one]
      _ = D 1 * 1 + 1 * D 1 := hD.2 1 1
      _ = D 1 + D 1 := by rw [mul_one, one_mul]
  apply add_left_cancel (b := D 1)
  rw [← hmul, add_zero]

def dlog (D : A → A) (u : Aˣ) : A :=
  (u⁻¹ : Aˣ).val * D (u : A)

theorem derivation_inv (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    D (u⁻¹ : Aˣ).val =
      - (u⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val * D (u : A) := by
  have h_one : (u : A) * (u⁻¹ : Aˣ).val = 1 := Units.mul_inv u
  have h_prod : D ((u : A) * (u⁻¹ : Aˣ).val) = 0 := by
    rw [h_one, derivation_one D hD]
  have h_leib := hD.2 (u : A) (u⁻¹ : Aˣ).val
  rw [h_prod] at h_leib
  have h_shift : (u : A) * D (u⁻¹ : Aˣ).val =
      -D (u : A) * (u⁻¹ : Aˣ).val := by
    linear_combination h_leib.symm
  calc
    D (u⁻¹ : Aˣ).val = 1 * D (u⁻¹ : Aˣ).val := by rw [one_mul]
    _ = ((u⁻¹ : Aˣ).val * (u : A)) * D (u⁻¹ : Aˣ).val := by
      rw [Units.inv_mul]
    _ = (u⁻¹ : Aˣ).val * ((u : A) * D (u⁻¹ : Aˣ).val) := by rw [mul_assoc]
    _ = (u⁻¹ : Aˣ).val * (-D (u : A) * (u⁻¹ : Aˣ).val) := by rw [h_shift]
    _ = - (u⁻¹ : Aˣ).val * (u⁻¹ : Aˣ).val * D (u : A) := by ring

theorem dlog_mul (D : A → A) (hD : IsDerivation D) (u v : Aˣ) :
    dlog D (u * v) = dlog D u + dlog D v := by
  dsimp [dlog]
  rw [hD.2 (u : A) (v : A)]
  have h_inv : ((u * v)⁻¹ : Aˣ).val =
      (u⁻¹ : Aˣ).val * (v⁻¹ : Aˣ).val := by
    rw [mul_inv_rev, Units.val_mul, mul_comm]
  rw [h_inv]
  have hu : (u⁻¹ : Aˣ).val * (u : A) = 1 := Units.inv_mul u
  have hv : (v⁻¹ : Aˣ).val * (v : A) = 1 := Units.inv_mul v
  calc
    (u⁻¹ : Aˣ).val * (v⁻¹ : Aˣ).val *
          (D (u : A) * (v : A) + (u : A) * D (v : A)) =
        ((u⁻¹ : Aˣ).val * D (u : A)) *
            ((v⁻¹ : Aˣ).val * (v : A)) +
          ((v⁻¹ : Aˣ).val * D (v : A)) *
            ((u⁻¹ : Aˣ).val * (u : A)) := by ring
    _ = (u⁻¹ : Aˣ).val * D (u : A) +
          (v⁻¹ : Aˣ).val * D (v : A) := by rw [hv, hu, mul_one, mul_one]

@[simp] theorem dlog_one (D : A → A) (hD : IsDerivation D) :
    dlog D 1 = 0 := by
  dsimp [dlog]
  rw [derivation_one D hD, mul_zero]

theorem dlog_inv (D : A → A) (hD : IsDerivation D) (u : Aˣ) :
    dlog D (u⁻¹) = -dlog D u := by
  have h := dlog_mul D hD u u⁻¹
  rw [mul_inv_cancel, dlog_one D hD] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem radon_nikodym_cocycle_dlog
    (D : A → A) (hD : IsDerivation D) (rho₁₂ rho₂₃ : Aˣ) :
    dlog D (rho₁₂ * rho₂₃) = dlog D rho₁₂ + dlog D rho₂₃ :=
  dlog_mul D hD rho₁₂ rho₂₃

end InfoGeometry.Algebra.ExplogRN
