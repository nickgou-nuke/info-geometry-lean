import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import InfoGeometry.Algebra.NonAssocIteratedLeibniz
import InfoGeometry.Algebra.NilpotentNonAssocDerivationExp

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset
open BigOperators

namespace InfoGeometry.Algebra.PeirceTransport

/-!
# Complete Peirce Frame Closure and Automorphism Transport

This module provides the complete native formalization of:
1. **Peirce Frame Identities** (without assuming associativity):
   - `ePlus_add_eMinus`: Resolution of identity ($e_+ + e_- = 1$).
   - `ePlus_idempotent` & `eMinus_idempotent`: Idempotency ($e_\pm \star e_\pm = e_\pm$).
   - `ePlus_mul_eMinus` & `eMinus_mul_ePlus`: Mutual orthogonality in both orientations ($e_+ \star e_- = 0$ and $e_- \star e_+ = 0$).
2. **Multiplicative Automorphism Transport**:
   - Preserves all algebraic Peirce relations under any `NonAssocAlgEquiv`.
3. **Derivation Stabilizer Sector Invariance**:
   - For an exponential flow $U_t = \exp(tD)$, $D(I) = 0$ strictly implies $U_t(I) = I$, $U_t(e_+) = e_+$, and $U_t(e_-) = e_-$.
-/

variable {F : Type*} [Field F] [CharZero F]
variable {A : Type*} [AddCommGroup A] [Module F A]
variable (mul : A →ₗ[F] A →ₗ[F] A)
variable (one : A)

open NonAssocIteratedLeibniz
open NilpotentDerivation

/-- The normalized half-scalar in the base field. -/
def half : F := (2 : F)⁻¹

theorem half_two : (2 : F) * (half : F) = (1 : F) := by
  dsimp [half]
  exact mul_inv_cancel₀ (by norm_num)

/-- Primitive positive Peirce idempotent: e₊ = ½(1 + I). -/
def ePlus (I : A) : A :=
  (half : F) • (one + I)

/-- Primitive negative Peirce idempotent: e₋ = ½(1 - I). -/
def eMinus (I : A) : A :=
  (half : F) • (one - I)

/-- 🏆 THEOREM: Resolution of identity: e₊ + e₋ = 1. -/
theorem ePlus_add_eMinus (I : A) :
    ePlus (F := F) one I + eMinus (F := F) one I = one := by
  dsimp [ePlus, eMinus]
  calc
    (half : F) • (one + I) + (half : F) • (one - I)
        = (half : F) • ((one + I) + (one - I)) := by rw [← smul_add]
      _ = (half : F) • (one + one + (I - I)) := by abel
      _ = (half : F) • (one + one + 0) := by rw [sub_self]
      _ = (half : F) • (one + one) := by rw [add_zero]
      _ = (half : F) • ((2 : F) • one) := by
        congr 1
        calc
          one + one = (1 : F) • one + (1 : F) • one := by rw [one_smul]
          _ = (1 + 1 : F) • one := by rw [add_smul]
          _ = (2 : F) • one := by norm_num
      _ = ((half : F) * (2 : F)) • one := by rw [smul_smul]
      _ = (1 : F) • one := by
        have h : (half : F) * 2 = 1 := by
          dsimp [half]
          exact inv_mul_cancel₀ (by norm_num)
        rw [h]
      _ = one := by rw [one_smul]

/-- 🏆 THEOREM: Idempotency of e₊: e₊ ⋆ e₊ = e₊. -/
theorem ePlus_idempotent
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (I : A) (hI_sq : mul I I = one) :
    mul (ePlus (F := F) one I) (ePlus (F := F) one I) = ePlus (F := F) one I := by
  dsimp [ePlus]
  have h_two_half : (2 : F) * (half : F) = 1 := half_two
  calc
    mul ((half : F) • (one + I)) ((half : F) • (one + I))
        = ((half : F) * (half : F)) • mul (one + I) (one + I) := by
          rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
      _ = ((half : F) * (half : F)) • ((mul one one + mul one I) + (mul I one + mul I I)) := by
          rw [LinearMap.map_add₂, LinearMap.map_add, LinearMap.map_add]
      _ = ((half : F) * (half : F)) • (one + I + I + one) := by
          rw [h_unit_left, h_unit_left, h_unit_right, hI_sq]
          congr 1
          abel
      _ = ((half : F) * (half : F)) • ((2 : F) • (one + I)) := by
          congr 1
          calc
            one + I + I + one = (one + I) + (one + I) := by abel
            _ = (1 : F) • (one + I) + (1 : F) • (one + I) := by rw [one_smul]
            _ = (1 + 1 : F) • (one + I) := by rw [add_smul]
            _ = (2 : F) • (one + I) := by norm_num
      _ = (((half : F) * (half : F)) * (2 : F)) • (one + I) := by rw [smul_smul]
      _ = ((half : F) * ((2 : F) * (half : F))) • (one + I) := by
          congr 1
          ring
      _ = ((half : F) * 1) • (one + I) := by rw [h_two_half]
      _ = (half : F) • (one + I) := by rw [mul_one]

/-- 🏆 THEOREM: Idempotency of e₋: e₋ ⋆ e₋ = e₋. -/
theorem eMinus_idempotent
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (I : A) (hI_sq : mul I I = one) :
    mul (eMinus (F := F) one I) (eMinus (F := F) one I) = eMinus (F := F) one I := by
  dsimp [eMinus]
  have h_two_half : (2 : F) * (half : F) = 1 := half_two
  calc
    mul ((half : F) • (one - I)) ((half : F) • (one - I))
        = ((half : F) * (half : F)) • mul (one - I) (one - I) := by
          rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
      _ = ((half : F) * (half : F)) • (mul one one - mul one I - mul I one + mul I I) := by
          rw [LinearMap.map_sub₂, LinearMap.map_sub, LinearMap.map_sub]
          abel
      _ = ((half : F) * (half : F)) • (one - I - I + one) := by
          rw [h_unit_left, h_unit_left, h_unit_right, hI_sq]
      _ = ((half : F) * (half : F)) • ((2 : F) • (one - I)) := by
          congr 1
          calc
            one - I - I + one = (one - I) + (one - I) := by abel
            _ = (1 : F) • (one - I) + (1 : F) • (one - I) := by rw [one_smul]
            _ = (1 + 1 : F) • (one - I) := by rw [add_smul]
            _ = (2 : F) • (one - I) := by norm_num
      _ = (((half : F) * (half : F)) * (2 : F)) • (one - I) := by rw [smul_smul]
      _ = ((half : F) * ((2 : F) * (half : F))) • (one - I) := by
          congr 1
          ring
      _ = ((half : F) * 1) • (one - I) := by rw [h_two_half]
      _ = (half : F) • (one - I) := by rw [mul_one]

/-- 🏆 THEOREM: Left Orthogonality: e₊ ⋆ e₋ = 0. -/
theorem ePlus_mul_eMinus
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (I : A) (hI_sq : mul I I = one) :
    mul (ePlus (F := F) one I) (eMinus (F := F) one I) = 0 := by
  dsimp [ePlus, eMinus]
  calc
    mul ((half : F) • (one + I)) ((half : F) • (one - I))
        = ((half : F) * (half : F)) • mul (one + I) (one - I) := by
          rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
      _ = ((half : F) * (half : F)) • (mul one one - mul one I + mul I one - mul I I) := by
          rw [LinearMap.map_add₂, LinearMap.map_sub, LinearMap.map_sub]
          abel
      _ = ((half : F) * (half : F)) • (one - I + I - one) := by
          rw [h_unit_left, h_unit_left, h_unit_right, hI_sq]
      _ = ((half : F) * (half : F)) • 0 := by
          congr 1
          abel
      _ = 0 := smul_zero _

/-- 🏆 THEOREM: Right Orthogonality: e₋ ⋆ e₊ = 0. -/
theorem eMinus_mul_ePlus
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (I : A) (hI_sq : mul I I = one) :
    mul (eMinus (F := F) one I) (ePlus (F := F) one I) = 0 := by
  dsimp [ePlus, eMinus]
  calc
    mul ((half : F) • (one - I)) ((half : F) • (one + I))
        = ((half : F) * (half : F)) • mul (one - I) (one + I) := by
          rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
      _ = ((half : F) * (half : F)) • (mul one one + mul one I - mul I one - mul I I) := by
          rw [LinearMap.map_sub₂, LinearMap.map_add, LinearMap.map_add]
          abel
      _ = ((half : F) * (half : F)) • (one + I - I - one) := by
          rw [h_unit_left, h_unit_left, h_unit_right, hI_sq]
      _ = ((half : F) * (half : F)) • 0 := by
          congr 1
          abel
      _ = 0 := smul_zero _

/-!
=============================================================================
PART 2: Multiplicative Automorphism Transport of Peirce Relations
=============================================================================
-/

/-- Idempotency transport under any NonAssocAlgEquiv. -/
theorem transport_ePlus_idempotent
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (e : NilpotentDerivation.NonAssocAlgEquiv mul one) (I : A) (hI_sq : mul I I = one) :
    mul (e (ePlus (F := F) one I)) (e (ePlus (F := F) one I)) = e (ePlus (F := F) one I) := by
  rw [← e.map_mul, ePlus_idempotent mul one h_unit_left h_unit_right I hI_sq]

theorem transport_eMinus_idempotent
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (e : NilpotentDerivation.NonAssocAlgEquiv mul one) (I : A) (hI_sq : mul I I = one) :
    mul (e (eMinus (F := F) one I)) (e (eMinus (F := F) one I)) = e (eMinus (F := F) one I) := by
  rw [← e.map_mul, eMinus_idempotent mul one h_unit_left h_unit_right I hI_sq]

/-- Both orientations of orthogonality transported under NonAssocAlgEquiv. -/
theorem transport_ePlus_mul_eMinus
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (e : NilpotentDerivation.NonAssocAlgEquiv mul one) (I : A) (hI_sq : mul I I = one) :
    mul (e (ePlus (F := F) one I)) (e (eMinus (F := F) one I)) = 0 := by
  rw [← e.map_mul, ePlus_mul_eMinus mul one h_unit_left h_unit_right I hI_sq, e.map_zero]

theorem transport_eMinus_mul_ePlus
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (e : NilpotentDerivation.NonAssocAlgEquiv mul one) (I : A) (hI_sq : mul I I = one) :
    mul (e (eMinus (F := F) one I)) (e (ePlus (F := F) one I)) = 0 := by
  rw [← e.map_mul, eMinus_mul_ePlus mul one h_unit_left h_unit_right I hI_sq, e.map_zero]

/-- Resolution of identity transported under NonAssocAlgEquiv. -/
theorem transport_resolution_of_identity
    (e : NilpotentDerivation.NonAssocAlgEquiv mul one) (I : A) :
    e (ePlus (F := F) one I) + e (eMinus (F := F) one I) = one := by
  rw [← e.map_add, ePlus_add_eMinus one I, e.map_one]

/-!
=============================================================================
PART 3: Derivation Stabilizer Sector Invariance
=============================================================================
-/

/-- Stabilizer invariance for the exponential flow: D(I) = 0 implies U_t(e₊) = e₊. -/
theorem expD2_ePlus_fixed_of_deriv_zero
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (D : A →ₗ[F] A)
    (hD_deriv : IsDerivation mul D)
    (t : F) (I : A) (hDI : D I = 0) :
    expD2 D t (ePlus (F := F) one I) = ePlus (F := F) one I := by
  dsimp [ePlus]
  have hI_fixed : expD2 D t I = I := expD2_fixed_of_deriv_zero D t I hDI
  have h_one_fixed : expD2 D t one = one := expD2_map_one mul one D h_unit_left h_unit_right hD_deriv t
  calc
    expD2 D t ((half : F) • (one + I))
        = (half : F) • expD2 D t (one + I) := by rw [map_smul]
      _ = (half : F) • (expD2 D t one + expD2 D t I) := by rw [map_add]
      _ = (half : F) • (one + I) := by rw [h_one_fixed, hI_fixed]

/-- Stabilizer invariance for the exponential flow: D(I) = 0 implies U_t(e₋) = e₋. -/
theorem expD2_eMinus_fixed_of_deriv_zero
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (D : A →ₗ[F] A)
    (hD_deriv : IsDerivation mul D)
    (t : F) (I : A) (hDI : D I = 0) :
    expD2 D t (eMinus (F := F) one I) = eMinus (F := F) one I := by
  dsimp [eMinus]
  have hI_fixed : expD2 D t I = I := expD2_fixed_of_deriv_zero D t I hDI
  have h_one_fixed : expD2 D t one = one := expD2_map_one mul one D h_unit_left h_unit_right hD_deriv t
  calc
    expD2 D t ((half : F) • (one - I))
        = (half : F) • expD2 D t (one - I) := by rw [map_smul]
      _ = (half : F) • (expD2 D t one - expD2 D t I) := by rw [map_sub]
      _ = (half : F) • (one - I) := by rw [h_one_fixed, hI_fixed]

end InfoGeometry.Algebra.PeirceTransport
