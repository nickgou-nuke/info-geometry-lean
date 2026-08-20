import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import InfoGeometry.Algebra.NonAssocIteratedLeibniz

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset
open BigOperators

namespace InfoGeometry.Algebra.NilpotentDerivation

/-!
# Nilpotent Non-Associative Derivation Exponential Automorphisms

This module constructs genuine algebra automorphisms from nilpotent derivations:
1. `NonAssocAlgEquiv`: Unital, multiplicative linear equivalences (`A ≃ₗ[F] A`).
2. `expD2`: The 1-parameter flow `U_t = I + t • D` for square-nilpotent derivations ($D^2 = 0$).
3. Complete proofs of:
   - Group laws: `U_0 = I`, `U_s ∘ U_t = U_{s+t}`, `U_{-t} ∘ U_t = I`.
   - Product homomorphism: `U_t(x ⋆ y) = (U_t x) ⋆ (U_t y)`.
   - Unit preservation: `U_t(1) = 1`.
   - Stabilizer action: `D(I) = 0 → U_t(I) = I`.
-/

variable {F : Type*} [Field F] [CharZero F]
variable {A : Type*} [AddCommGroup A] [Module F A]
variable (mul : A →ₗ[F] A →ₗ[F] A)
variable (one : A)

open NonAssocIteratedLeibniz

/-- An invertible linear map that preserves multiplication and unit. -/
structure NonAssocAlgEquiv (mul : A →ₗ[F] A →ₗ[F] A) (one : A) extends A ≃ₗ[F] A where
  map_mul' : ∀ x y : A, toLinearEquiv (mul x y) = mul (toLinearEquiv x) (toLinearEquiv y)
  map_one' : toLinearEquiv one = one

namespace NonAssocAlgEquiv

instance : CoeFun (NonAssocAlgEquiv mul one) (fun _ => A → A) where
  coe e := e.toLinearEquiv

variable {mul one}

@[simp] theorem map_mul (e : NonAssocAlgEquiv mul one) (x y : A) :
    e (mul x y) = mul (e x) (e y) :=
  e.map_mul' x y

@[simp] theorem map_one (e : NonAssocAlgEquiv mul one) :
    e one = one :=
  e.map_one'

@[simp] theorem map_zero (e : NonAssocAlgEquiv mul one) :
    e 0 = 0 :=
  e.toLinearEquiv.map_zero

@[simp] theorem map_add (e : NonAssocAlgEquiv mul one) (x y : A) :
    e (x + y) = e x + e y :=
  e.toLinearEquiv.map_add x y

@[simp] theorem map_smul (e : NonAssocAlgEquiv mul one) (c : F) (x : A) :
    e (c • x) = c • e x :=
  e.toLinearEquiv.map_smul c x

/-- The inverse equivalence. -/
def symm (e : NonAssocAlgEquiv mul one) : NonAssocAlgEquiv mul one where
  toLinearEquiv := e.toLinearEquiv.symm
  map_mul' x y := by
    have h : e (e.toLinearEquiv.symm (mul x y)) = e (mul (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm y)) := by
      rw [e.toLinearEquiv.apply_symm_apply, e.map_mul,
          e.toLinearEquiv.apply_symm_apply, e.toLinearEquiv.apply_symm_apply]
    exact e.toLinearEquiv.injective h
  map_one' := by
    have h : e (e.toLinearEquiv.symm one) = e one := by
      rw [e.toLinearEquiv.apply_symm_apply, e.map_one]
    exact e.toLinearEquiv.injective h

@[simp] theorem symm_apply_apply (e : NonAssocAlgEquiv mul one) (x : A) :
    e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

@[simp] theorem apply_symm_apply (e : NonAssocAlgEquiv mul one) (x : A) :
    e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x

/-- Converting an equivalence to an endomorphism. -/
def toNonAssocAlgEnd (e : NonAssocAlgEquiv mul one) :
    NonAssocIteratedLeibniz.NonAssocAlgEnd mul one where
  toLinearMap := e.toLinearEquiv.toLinearMap
  map_mul' := e.map_mul'
  map_one' := e.map_one'

end NonAssocAlgEquiv

/-!
=============================================================================
PART 2: Square-Nilpotent Non-Associative Exponential Automorphisms (D² = 0)
=============================================================================
-/

/-- The 1-parameter linear map U_t = I + t • D. -/
def expD2 (D : A →ₗ[F] A) (t : F) : A →ₗ[F] A :=
  LinearMap.id + t • D

@[simp] theorem expD2_apply (D : A →ₗ[F] A) (t : F) (x : A) :
    expD2 D t x = x + t • D x := rfl

/-- Product composition law: U_s ∘ U_t = U_{s+t}. -/
theorem expD2_comp (D : A →ₗ[F] A) (hD_sq : D.comp D = 0) (s t : F) :
    (expD2 D s).comp (expD2 D t) = expD2 D (s + t) := by
  ext x
  dsimp [expD2]
  have h_sq : D (D x) = 0 := by
    have h := LinearMap.congr_fun hD_sq x
    exact h
  simp only [map_add, map_smul, h_sq, smul_zero, add_zero]
  rw [add_assoc, ← add_smul, add_comm t s]

/-- Identity at t = 0: U_0 = I. -/
@[simp] theorem expD2_zero (D : A →ₗ[F] A) :
    expD2 D 0 = LinearMap.id := by
  ext x
  dsimp [expD2]
  have h_zero : (0 : F) • D x = 0 := zero_smul F (D x)
  rw [h_zero, add_zero]

/-- Inverse relation: U_{-t} ∘ U_t = I. -/
theorem expD2_inv (D : A →ₗ[F] A) (hD_sq : D.comp D = 0) (t : F) :
    (expD2 D (-t)).comp (expD2 D t) = LinearMap.id := by
  rw [expD2_comp D hD_sq, neg_add_cancel, expD2_zero]

theorem expD2_inv' (D : A →ₗ[F] A) (hD_sq : D.comp D = 0) (t : F) :
    (expD2 D t).comp (expD2 D (-t)) = LinearMap.id := by
  rw [expD2_comp D hD_sq, add_neg_cancel, expD2_zero]

theorem expD2_add_apply (D : A →ₗ[F] A) (hD_sq : D.comp D = 0)
    (s t : F) (x : A) :
    expD2 D (s + t) x = expD2 D s (expD2 D t x) := by
  have h := LinearMap.congr_fun (expD2_comp D hD_sq s t) x
  exact h.symm

/-- Exponential as a linear equivalence. -/
def expD2LinearEquiv (D : A →ₗ[F] A) (hD_sq : D.comp D = 0) (t : F) : A ≃ₗ[F] A where
  toFun := expD2 D t
  invFun := expD2 D (-t)
  left_inv x := by
    have h := LinearMap.congr_fun (expD2_inv D hD_sq t) x
    exact h
  right_inv x := by
    have h := LinearMap.congr_fun (expD2_comp D hD_sq t (-t)) x
    rw [add_neg_cancel, expD2_zero] at h
    exact h
  map_add' x y := (expD2 D t).map_add x y
  map_smul' c x := (expD2 D t).map_smul c x

/-- 🏆 THEOREM: Product preservation:
    U_t(x ⋆ y) = (U_t x) ⋆ (U_t y) -/
theorem expD2_map_mul (D : A →ₗ[F] A) (hD_deriv : IsDerivation mul D)
    (hD_cross : ∀ x y : A, mul (D x) (D y) = 0) (t : F) (x y : A) :
    expD2 D t (mul x y) = mul (expD2 D t x) (expD2 D t y) := by
  dsimp [expD2]
  rw [hD_deriv x y]
  have h_cross : mul (D x) (D y) = 0 := hD_cross x y
  calc
    mul x y + t • (mul (D x) y + mul x (D y))
        = mul x y + t • mul (D x) y + t • mul x (D y) + 0 := by
          rw [smul_add, add_zero]
          abel
      _ = mul x y + t • mul (D x) y + t • mul x (D y) + (t * t) • mul (D x) (D y) := by
          rw [h_cross, smul_zero]
      _ = mul (x + t • D x) (y + t • D y) := by
          rw [LinearMap.map_add₂, LinearMap.map_add, LinearMap.map_add]
          rw [LinearMap.map_smul₂, LinearMap.map_smul, LinearMap.map_smul₂, LinearMap.map_smul]
          rw [smul_smul]
          abel

/-- 🏆 THEOREM: Unit preservation:
    U_t(1) = 1 -/
theorem expD2_map_one (D : A →ₗ[F] A)
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (hD_deriv : IsDerivation mul D) (t : F) :
    expD2 D t one = one := by
  dsimp [expD2]
  have h1 : D one = 0 := derivation_kills_one mul D one h_unit_left h_unit_right hD_deriv
  rw [h1, smul_zero, add_zero]

/-- 🏆 MASTER CONSTRUCTOR: The Certified Exponential Automorphism -/
def expD2AlgEquiv (D : A →ₗ[F] A)
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (hD_deriv : IsDerivation mul D)
    (hD_sq : D.comp D = 0)
    (hD_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : F) : NonAssocAlgEquiv mul one where
  toLinearEquiv := expD2LinearEquiv D hD_sq t
  map_mul' := expD2_map_mul mul D hD_deriv hD_cross t
  map_one' := expD2_map_one mul one D h_unit_left h_unit_right hD_deriv t

/-- Stabilizer Action: D(I) = 0 → U_t(I) = I -/
theorem expD2_fixed_of_deriv_zero (D : A →ₗ[F] A) (t : F) (I : A) (hDI : D I = 0) :
    expD2 D t I = I := by
  dsimp [expD2]
  rw [hDI, smul_zero, add_zero]

end InfoGeometry.Algebra.NilpotentDerivation
