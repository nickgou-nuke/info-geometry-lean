import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import InfoGeometry.Algebra.NonAssocIteratedLeibniz
import InfoGeometry.Algebra.NilpotentNonAssocDerivationExp

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset
open BigOperators
open InfoGeometry.Algebra.NonAssocIteratedLeibniz
open InfoGeometry.Algebra.NilpotentNonAssocDerivationExp

namespace InfoGeometry.Algebra.PeirceTransport

/-!
# Complete Peirce Frame Closure and Automorphism Transport

This module provides the complete native formalization of:
1. **Peirce Frame Identities** (without assuming associativity):
   - `ePlus_add_eMinus`: Resolution of identity ($e_+ + e_- = 1$).
   - `ePlus_idempotent` & `eMinus_idempotent`: Idempotency ($e_\pm \star e_\pm = e_\pm$).
   - `ePlus_mul_eMinus` & `eMinus_mul_ePlus`: Mutual orthogonality in both orientations ($e_+ \star e_- = 0$ and $e_- \star e_+ = 0$).
2. **Multiplicative Automorphism Transport**:
   - Preserves all algebraic Peirce relations under any `NonAssocAlgEnd`.
3. **Derivation Stabilizer Sector Invariance**:
   - For an exponential flow $U_t = \exp(tD)$, $D(I) = 0$ strictly implies $U_t(I) = I$, $U_t(e_+) = e_+$, and $U_t(e_-) = e_-$.
-/

variable {K A : Type*} [Field K] [CharZero K] [AddCommGroup A] [Module K A]
variable (mul : A →ₗ[K] A →ₗ[K] A)
variable (one : A)

/-- The normalized half-scalar in the base field. -/
def half : K := (2 : K)⁻¹

theorem half_two : (2 : K) * (half : K) = (1 : K) := by
  dsimp [half]
  exact mul_inv_cancel₀ (by norm_num)

/-- Primitive positive Peirce idempotent: e₊ = ½(1 + I). -/
def ePlus (I : A) : A :=
  (half : K) • (one + I)

/-- Primitive negative Peirce idempotent: e₋ = ½(1 - I). -/
def eMinus (I : A) : A :=
  (half : K) • (one - I)

/-- 🏆 THEOREM: Resolution of identity: e₊ + e₋ = 1. -/
theorem ePlus_add_eMinus (I : A) :
    ePlus (K := K) one I + eMinus (K := K) one I = one := by
  dsimp [ePlus, eMinus]
  calc
    (half : K) • (one + I) + (half : K) • (one - I)
        = (half : K) • ((one + I) + (one - I)) := by rw [← smul_add]
      _ = (half : K) • (one + one + (I - I)) := by
        congr 1
        abel_nf
      _ = (half : K) • (one + one + 0) := by rw [sub_self]
      _ = (half : K) • (one + one) := by rw [add_zero]
      _ = (half : K) • ((2 : K) • one) := by
        congr 1
        calc
          one + one = (1 : K) • one + (1 : K) • one := by rw [one_smul]
          _ = (1 + 1 : K) • one := by rw [add_smul]
          _ = (2 : K) • one := by norm_num
      _ = ((half : K) * (2 : K)) • one := by rw [smul_smul]
      _ = (1 : K) • one := by
        have h : (half : K) * 2 = 1 := by
          dsimp [half]
          exact inv_mul_cancel₀ (by norm_num)
        rw [h]
      _ = one := by rw [one_smul]

/-- 🏆 THEOREM: Idempotency of e₊: e₊ ⋆ e₊ = e₊. -/
theorem ePlus_idempotent
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (I : A) (hI_sq : mul I I = one) :
    mul (ePlus (K := K) one I) (ePlus (K := K) one I) = ePlus (K := K) one I := by
  dsimp [ePlus]
  have h_two_half : (2 : K) * (half : K) = 1 := half_two
  calc
    mul ((half : K) • (one + I)) ((half : K) • (one + I))
        = ((half : K) * (half : K)) • mul (one + I) (one + I) := by
          rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
      _ = ((half : K) * (half : K)) • ((mul one one + mul one I) + (mul I one + mul I I)) := by
          rw [LinearMap.map_add₂, LinearMap.map_add, LinearMap.map_add]
      _ = ((half : K) * (half : K)) • (one + I + I + one) := by
          rw [h_unit_left, h_unit_left, h_unit_right, hI_sq]
          congr 1
          abel
      _ = ((half : K) * (half : K)) • ((2 : K) • (one + I)) := by
          congr 1
          calc
            one + I + I + one = (one + I) + (one + I) := by abel
            _ = (1 : K) • (one + I) + (1 : K) • (one + I) := by rw [one_smul]
            _ = (1 + 1 : K) • (one + I) := by rw [add_smul]
            _ = (2 : K) • (one + I) := by norm_num
      _ = (((half : K) * (half : K)) * (2 : K)) • (one + I) := by rw [smul_smul]
      _ = ((half : K) * ((2 : K) * (half : K))) • (one + I) := by
          congr 1
          ring
      _ = ((half : K) * 1) • (one + I) := by rw [h_two_half]
      _ = (half : K) • (one + I) := by rw [mul_one]

/-- 🏆 THEOREM: Idempotency of e₋: e₋ ⋆ e₋ = e₋. -/
theorem eMinus_idempotent
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (I : A) (hI_sq : mul I I = one) :
    mul (eMinus (K := K) one I) (eMinus (K := K) one I) = eMinus (K := K) one I := by
  dsimp [eMinus]
  have h_two_half : (2 : K) * (half : K) = 1 := half_two
  have h_expand : mul (one - I) (one - I) = mul one one - mul one I - mul I one + mul I I := by
    rw [LinearMap.map_sub₂, LinearMap.map_sub, LinearMap.map_sub]
    abel
  calc
    mul ((half : K) • (one - I)) ((half : K) • (one - I))
        = ((half : K) * (half : K)) • mul (one - I) (one - I) := by
          rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
      _ = ((half : K) * (half : K)) • (mul one one - mul one I - mul I one + mul I I) := by
          rw [h_expand]
      _ = ((half : K) * (half : K)) • (one - I - I + one) := by
          rw [h_unit_left, h_unit_left, h_unit_right, hI_sq]
      _ = ((half : K) * (half : K)) • ((2 : K) • (one - I)) := by
          congr 1
          calc
            one - I - I + one = (one - I) + (one - I) := by abel
            _ = (1 : K) • (one - I) + (1 : K) • (one - I) := by rw [one_smul]
            _ = (1 + 1 : K) • (one - I) := by rw [add_smul]
            _ = (2 : K) • (one - I) := by norm_num
      _ = (((half : K) * (half : K)) * (2 : K)) • (one - I) := by rw [smul_smul]
      _ = ((half : K) * ((2 : K) * (half : K))) • (one - I) := by
          congr 1
          ring
      _ = ((half : K) * 1) • (one - I) := by rw [h_two_half]
      _ = (half : K) • (one - I) := by rw [mul_one]

/-- 🏆 THEOREM: Left Orthogonality: e₊ ⋆ e₋ = 0. -/
theorem ePlus_mul_eMinus
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (I : A) (hI_sq : mul I I = one) :
    mul (ePlus (K := K) one I) (eMinus (K := K) one I) = 0 := by
  dsimp [ePlus, eMinus]
  have h_expand : mul (one + I) (one - I) = mul one one - mul one I + mul I one - mul I I := by
    rw [LinearMap.map_add₂, LinearMap.map_sub, LinearMap.map_sub]
    abel
  calc
    mul ((half : K) • (one + I)) ((half : K) • (one - I))
        = ((half : K) * (half : K)) • mul (one + I) (one - I) := by
          rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
      _ = ((half : K) * (half : K)) • (mul one one - mul one I + mul I one - mul I I) := by
          rw [h_expand]
      _ = ((half : K) * (half : K)) • (one - I + I - one) := by
          rw [h_unit_left, h_unit_left, h_unit_right, hI_sq]
      _ = ((half : K) * (half : K)) • 0 := by
          congr 1
          abel
      _ = 0 := smul_zero _

/-- 🏆 THEOREM: Right Orthogonality: e₋ ⋆ e₊ = 0. -/
theorem eMinus_mul_ePlus
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (I : A) (hI_sq : mul I I = one) :
    mul (eMinus (K := K) one I) (ePlus (K := K) one I) = 0 := by
  dsimp [ePlus, eMinus]
  have h_expand : mul (one - I) (one + I) = mul one one + mul one I - mul I one - mul I I := by
    rw [LinearMap.map_sub₂, LinearMap.map_add, LinearMap.map_add]
    abel
  calc
    mul ((half : K) • (one - I)) ((half : K) • (one + I))
        = ((half : K) * (half : K)) • mul (one - I) (one + I) := by
          rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
      _ = ((half : K) * (half : K)) • (mul one one + mul one I - mul I one - mul I I) := by
          rw [h_expand]
      _ = ((half : K) * (half : K)) • (one + I - I - one) := by
          rw [h_unit_left, h_unit_left, h_unit_right, hI_sq]
      _ = ((half : K) * (half : K)) • 0 := by
          congr 1
          abel
      _ = 0 := smul_zero _

/-!
=============================================================================
PART 2: Multiplicative Transport of Peirce Relations
=============================================================================
-/

/-- Idempotency transport under any NonAssocAlgEnd. -/
theorem transport_ePlus_idempotent
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (Φ : NonAssocAlgEnd mul one) (I : A) (hI_sq : mul I I = one) :
    mul (Φ (ePlus (K := K) one I)) (Φ (ePlus (K := K) one I)) = Φ (ePlus (K := K) one I) := by
  rw [← Φ.map_mul, ePlus_idempotent mul one h_unit_left h_unit_right I hI_sq]

theorem transport_eMinus_idempotent
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (Φ : NonAssocAlgEnd mul one) (I : A) (hI_sq : mul I I = one) :
    mul (Φ (eMinus (K := K) one I)) (Φ (eMinus (K := K) one I)) = Φ (eMinus (K := K) one I) := by
  rw [← Φ.map_mul, eMinus_idempotent mul one h_unit_left h_unit_right I hI_sq]

/-- Both orientations of orthogonality transported under NonAssocAlgEnd. -/
theorem transport_ePlus_mul_eMinus
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (Φ : NonAssocAlgEnd mul one) (I : A) (hI_sq : mul I I = one) :
    mul (Φ (ePlus (K := K) one I)) (Φ (eMinus (K := K) one I)) = 0 := by
  rw [← Φ.map_mul, ePlus_mul_eMinus mul one h_unit_left h_unit_right I hI_sq, Φ.map_zero]

theorem transport_eMinus_mul_ePlus
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (Φ : NonAssocAlgEnd mul one) (I : A) (hI_sq : mul I I = one) :
    mul (Φ (eMinus (K := K) one I)) (Φ (ePlus (K := K) one I)) = 0 := by
  rw [← Φ.map_mul, eMinus_mul_ePlus mul one h_unit_left h_unit_right I hI_sq, Φ.map_zero]

/-- Resolution of identity transported under NonAssocAlgEnd. -/
theorem transport_resolution_of_identity
    (Φ : NonAssocAlgEnd mul one) (I : A) :
    Φ (ePlus (K := K) one I) + Φ (eMinus (K := K) one I) = one := by
  rw [← Φ.toLinearMap.map_add, ePlus_add_eMinus (K := K) one I, Φ.map_one]

/-!
=============================================================================
PART 3: Derivation Stabilizer Sector Invariance
=============================================================================
-/

/-- Stabilizer invariance for the exponential flow: D(I) = 0 implies U_t(e₊) = e₊. -/
theorem expStep2_ePlus_fixed_of_deriv_zero
    (D : A →ₗ[K] A)
    (hD_one : D one = 0)
    (t : K) (I : A) (hDI : D I = 0) :
    nilpotentExpStep2 D t (ePlus (K := K) one I) = ePlus (K := K) one I := by
  dsimp [ePlus]
  have hI_fixed : nilpotentExpStep2 D t I = I := by
    simp [nilpotentExpStep2_apply, hDI]
  have h_one_fixed : nilpotentExpStep2 D t one = one :=
    nilpotentExpStep2_one one D t hD_one
  calc
    nilpotentExpStep2 D t ((half : K) • (one + I))
        = (half : K) • nilpotentExpStep2 D t (one + I) := by
          exact (nilpotentExpStep2 D t).map_smul (half : K) (one + I)
      _ = (half : K) • (nilpotentExpStep2 D t one + nilpotentExpStep2 D t I) := by
          rw [(nilpotentExpStep2 D t).map_add]
      _ = (half : K) • (one + I) := by rw [h_one_fixed, hI_fixed]

/-- Stabilizer invariance for the exponential flow: D(I) = 0 implies U_t(e₋) = e₋. -/
theorem expStep2_eMinus_fixed_of_deriv_zero
    (D : A →ₗ[K] A)
    (hD_one : D one = 0)
    (t : K) (I : A) (hDI : D I = 0) :
    nilpotentExpStep2 D t (eMinus (K := K) one I) = eMinus (K := K) one I := by
  dsimp [eMinus]
  have hI_fixed : nilpotentExpStep2 D t I = I := by
    simp [nilpotentExpStep2_apply, hDI]
  have h_one_fixed : nilpotentExpStep2 D t one = one :=
    nilpotentExpStep2_one one D t hD_one
  calc
    nilpotentExpStep2 D t ((half : K) • (one - I))
        = (half : K) • nilpotentExpStep2 D t (one - I) := by
          exact (nilpotentExpStep2 D t).map_smul (half : K) (one - I)
      _ = (half : K) • (nilpotentExpStep2 D t one - nilpotentExpStep2 D t I) := by
          rw [(nilpotentExpStep2 D t).map_sub]
      _ = (half : K) • (one - I) := by rw [h_one_fixed, hI_fixed]

end InfoGeometry.Algebra.PeirceTransport
