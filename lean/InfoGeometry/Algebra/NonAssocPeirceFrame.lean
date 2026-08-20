import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Non-Associative Peirce Frame and Multiplicative Transport

This module provides a fully closed, zero-axiom formalization of:
1. Primitive Peirce idempotents and their complete algebraic relations:
   - `ePlus ⋆ ePlus = ePlus`
   - `eMinus ⋆ eMinus = eMinus`
   - `ePlus ⋆ eMinus = 0` (left orthogonality)
   - `eMinus ⋆ ePlus = 0` (right orthogonality)
   - `ePlus + eMinus = 1` (resolution of identity)
2. Certified multiplicative transport:
   - Automatic relation preservation under `NonAssocAlgEnd`
   - Invariance of chiral sheets under the stabilizer of `I` (`F I = I → F ePlus = ePlus`)

No associativity of the bilinear multiplication `mul` is assumed anywhere.
-/

noncomputable section

namespace InfoGeometry.Algebra.NonAssocPeirceFrame

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- A unital, non-associative R-algebra with bilinear multiplication -/
structure NonAssocUnitalAlgebra (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] where
  mul : A →ₗ[R] A →ₗ[R] A
  one : A
  one_mul : ∀ a : A, mul one a = a
  mul_one : ∀ a : A, mul a one = a

namespace NonAssocUnitalAlgebra

variable (alg : NonAssocUnitalAlgebra R A)

/-- The positive chiral projector e₊ = half • (1 + I). -/
def ePlus (half : R) (I : A) : A :=
  half • (alg.one + I)

/-- The negative chiral projector e₋ = half • (1 - I). -/
def eMinus (half : R) (I : A) : A :=
  half • (alg.one - I)

/-- 
  THEOREM 1: Resolution of Identity
  e₊ + e₋ = 1
-/
theorem ePlus_add_eMinus (half : R) (h_half : (2 : R) * half = 1) (I : A) :
    alg.ePlus half I + alg.eMinus half I = alg.one := by
  dsimp [ePlus, eMinus]
  rw [← smul_add]
  have h_sum : (alg.one + I) + (alg.one - I) = (2 : R) • alg.one := by
    calc
      (alg.one + I) + (alg.one - I) = (alg.one + alg.one) + (I - I) := by abel
      _ = (2 : R) • alg.one + 0 := by
        simp only [two_smul, sub_self]
      _ = (2 : R) • alg.one := by rw [add_zero]
  rw [h_sum, smul_smul]
  have h_scalar : half * 2 = 1 := by
    rw [mul_comm, h_half]
  rw [h_scalar, one_smul]

/-- 
  THEOREM 2: Idempotency of e₊
  e₊ ⋆ e₊ = e₊
  Proven using only bilinearity, two-sided unit laws, and I ⋆ I = 1.
-/
theorem ePlus_idempotent (half : R) (h_half : (2 : R) * half = 1) (I : A) (hI : alg.mul I I = alg.one) :
    alg.mul (alg.ePlus half I) (alg.ePlus half I) = alg.ePlus half I := by
  dsimp [ePlus]
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  have h1 : alg.mul (alg.one + I) = alg.mul alg.one + alg.mul I := alg.mul.map_add alg.one I
  have h3 : alg.mul alg.one (alg.one + I) = alg.mul alg.one alg.one + alg.mul alg.one I := (alg.mul alg.one).map_add alg.one I
  have h4 : alg.mul I (alg.one + I) = alg.mul I alg.one + alg.mul I I := (alg.mul I).map_add alg.one I
  have h_prod : alg.mul (alg.one + I) (alg.one + I) = (2 : R) • (alg.one + I) := by
    calc
      alg.mul (alg.one + I) (alg.one + I)
        = (alg.mul alg.one + alg.mul I) (alg.one + I) := by rw [LinearMap.congr_fun h1 (alg.one + I)]
      _ = alg.mul alg.one (alg.one + I) + alg.mul I (alg.one + I) := rfl
      _ = alg.mul alg.one alg.one + alg.mul alg.one I + (alg.mul I alg.one + alg.mul I I) := by rw [h3, h4]
      _ = alg.one + I + (I + alg.one) := by rw [alg.one_mul, alg.one_mul, alg.mul_one, hI]
      _ = (2 : R) • (alg.one + I) := by
        simp only [two_smul, smul_add]
        abel
  rw [h_prod, smul_smul, smul_smul]
  have h_scal : half * half * 2 = half := by
    calc
      half * half * 2 = half * ((2 : R) * half) := by ring
      _ = half * 1 := by rw [h_half]
      _ = half := _root_.mul_one half
  rw [h_scal]

/-- 
  THEOREM 3: Idempotency of e₋
  e₋ ⋆ e₋ = e₋
-/
theorem eMinus_idempotent (half : R) (h_half : (2 : R) * half = 1) (I : A) (hI : alg.mul I I = alg.one) :
    alg.mul (alg.eMinus half I) (alg.eMinus half I) = alg.eMinus half I := by
  dsimp [eMinus]
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  have h1 : alg.mul (alg.one - I) = alg.mul alg.one - alg.mul I := alg.mul.map_sub alg.one I
  have h3 : alg.mul alg.one (alg.one - I) = alg.mul alg.one alg.one - alg.mul alg.one I := (alg.mul alg.one).map_sub alg.one I
  have h4 : alg.mul I (alg.one - I) = alg.mul I alg.one - alg.mul I I := (alg.mul I).map_sub alg.one I
  have h_prod : alg.mul (alg.one - I) (alg.one - I) = (2 : R) • (alg.one - I) := by
    calc
      alg.mul (alg.one - I) (alg.one - I)
        = (alg.mul alg.one - alg.mul I) (alg.one - I) := by rw [LinearMap.congr_fun h1 (alg.one - I)]
      _ = alg.mul alg.one (alg.one - I) - alg.mul I (alg.one - I) := rfl
      _ = alg.mul alg.one alg.one - alg.mul alg.one I - (alg.mul I alg.one - alg.mul I I) := by rw [h3, h4]
      _ = alg.one - I - (I - alg.one) := by rw [alg.one_mul, alg.one_mul, alg.mul_one, hI]
      _ = (2 : R) • (alg.one - I) := by
        simp only [two_smul, smul_sub]
        abel
  rw [h_prod, smul_smul, smul_smul]
  have h_scal : half * half * 2 = half := by
    calc
      half * half * 2 = half * ((2 : R) * half) := by ring
      _ = half * 1 := by rw [h_half]
      _ = half := _root_.mul_one half
  rw [h_scal]

/-- 
  THEOREM 4: Left Orthogonality
  e₊ ⋆ e₋ = 0
-/
theorem ePlus_mul_eMinus (half : R) (I : A) (hI : alg.mul I I = alg.one) :
    alg.mul (alg.ePlus half I) (alg.eMinus half I) = 0 := by
  dsimp [ePlus, eMinus]
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  have h1 : alg.mul (alg.one + I) = alg.mul alg.one + alg.mul I := alg.mul.map_add alg.one I
  have h3 : alg.mul alg.one (alg.one - I) = alg.mul alg.one alg.one - alg.mul alg.one I := (alg.mul alg.one).map_sub alg.one I
  have h4 : alg.mul I (alg.one - I) = alg.mul I alg.one - alg.mul I I := (alg.mul I).map_sub alg.one I
  have h_prod : alg.mul (alg.one + I) (alg.one - I) = 0 := by
    calc
      alg.mul (alg.one + I) (alg.one - I)
        = (alg.mul alg.one + alg.mul I) (alg.one - I) := by rw [LinearMap.congr_fun h1 (alg.one - I)]
      _ = alg.mul alg.one (alg.one - I) + alg.mul I (alg.one - I) := rfl
      _ = alg.mul alg.one alg.one - alg.mul alg.one I + (alg.mul I alg.one - alg.mul I I) := by rw [h3, h4]
      _ = alg.one - I + (I - alg.one) := by rw [alg.one_mul, alg.one_mul, alg.mul_one, hI]
      _ = 0 := by abel
  rw [h_prod, smul_zero, smul_zero]

/-- 
  THEOREM 5: Right Orthogonality
  e₋ ⋆ e₊ = 0
-/
theorem eMinus_mul_ePlus (half : R) (I : A) (hI : alg.mul I I = alg.one) :
    alg.mul (alg.eMinus half I) (alg.ePlus half I) = 0 := by
  dsimp [ePlus, eMinus]
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  have h1 : alg.mul (alg.one - I) = alg.mul alg.one - alg.mul I := alg.mul.map_sub alg.one I
  have h3 : alg.mul alg.one (alg.one + I) = alg.mul alg.one alg.one + alg.mul alg.one I := (alg.mul alg.one).map_add alg.one I
  have h4 : alg.mul I (alg.one + I) = alg.mul I alg.one + alg.mul I I := (alg.mul I).map_add alg.one I
  have h_prod : alg.mul (alg.one - I) (alg.one + I) = 0 := by
    calc
      alg.mul (alg.one - I) (alg.one + I)
        = (alg.mul alg.one - alg.mul I) (alg.one + I) := by rw [LinearMap.congr_fun h1 (alg.one + I)]
      _ = alg.mul alg.one (alg.one + I) - alg.mul I (alg.one + I) := rfl
      _ = alg.mul alg.one alg.one + alg.mul alg.one I - (alg.mul I alg.one + alg.mul I I) := by rw [h3, h4]
      _ = alg.one + I - (I + alg.one) := by rw [alg.one_mul, alg.one_mul, alg.mul_one, hI]
      _ = 0 := by abel
  rw [h_prod, smul_zero, smul_zero]

end NonAssocUnitalAlgebra

/-!
=============================================================================
PART 2: Certified Multiplicative Transport
=============================================================================
-/

/-- A unital multiplicative linear endomorphism of a non-associative algebra. -/
structure NonAssocAlgEnd (alg : NonAssocUnitalAlgebra R A) where
  toLinearMap : A →ₗ[R] A
  map_mul' : ∀ x y : A, toLinearMap (alg.mul x y) = alg.mul (toLinearMap x) (toLinearMap y)
  map_one' : toLinearMap alg.one = alg.one

namespace NonAssocAlgEnd

variable {alg : NonAssocUnitalAlgebra R A}

instance : CoeFun (NonAssocAlgEnd alg) (fun _ => A → A) where
  coe F := F.toLinearMap

@[simp] theorem map_mul (F : NonAssocAlgEnd alg) (x y : A) :
    F (alg.mul x y) = alg.mul (F x) (F y) :=
  F.map_mul' x y

@[simp] theorem map_one (F : NonAssocAlgEnd alg) :
    F alg.one = alg.one :=
  F.map_one'

@[simp] theorem map_zero (F : NonAssocAlgEnd alg) :
    F 0 = 0 :=
  F.toLinearMap.map_zero

@[simp] theorem map_add (F : NonAssocAlgEnd alg) (x y : A) :
    F (x + y) = F x + F y :=
  F.toLinearMap.map_add x y

@[simp] theorem map_sub (F : NonAssocAlgEnd alg) (x y : A) :
    F (x - y) = F x - F y :=
  F.toLinearMap.map_sub x y

@[simp] theorem map_smul (F : NonAssocAlgEnd alg) (c : R) (x : A) :
    F (c • x) = c • F x :=
  F.toLinearMap.map_smul c x

/-- THEOREM: Multiplicative maps preserve the positive idempotent. -/
theorem map_ePlus_idempotent (F : NonAssocAlgEnd alg) (half : R) (h_half : (2 : R) * half = 1)
    (I : A) (hI : alg.mul I I = alg.one) :
    alg.mul (F (alg.ePlus half I)) (F (alg.ePlus half I)) = F (alg.ePlus half I) := by
  rw [← F.map_mul, alg.ePlus_idempotent half h_half I hI]

/-- THEOREM: Multiplicative maps preserve the negative idempotent. -/
theorem map_eMinus_idempotent (F : NonAssocAlgEnd alg) (half : R) (h_half : (2 : R) * half = 1)
    (I : A) (hI : alg.mul I I = alg.one) :
    alg.mul (F (alg.eMinus half I)) (F (alg.eMinus half I)) = F (alg.eMinus half I) := by
  rw [← F.map_mul, alg.eMinus_idempotent half h_half I hI]

/-- THEOREM: Multiplicative maps preserve left orthogonality. -/
theorem map_ePlus_mul_eMinus (F : NonAssocAlgEnd alg) (half : R)
    (I : A) (hI : alg.mul I I = alg.one) :
    alg.mul (F (alg.ePlus half I)) (F (alg.eMinus half I)) = 0 := by
  rw [← F.map_mul, alg.ePlus_mul_eMinus half I hI, F.map_zero]

/-- THEOREM: Multiplicative maps preserve right orthogonality. -/
theorem map_eMinus_mul_ePlus (F : NonAssocAlgEnd alg) (half : R)
    (I : A) (hI : alg.mul I I = alg.one) :
    alg.mul (F (alg.eMinus half I)) (F (alg.ePlus half I)) = 0 := by
  rw [← F.map_mul, alg.eMinus_mul_ePlus half I hI, F.map_zero]

/-- THEOREM: Multiplicative maps preserve the resolution of identity. -/
theorem map_ePlus_add_eMinus (F : NonAssocAlgEnd alg) (half : R) (h_half : (2 : R) * half = 1) (I : A) :
    F (alg.ePlus half I) + F (alg.eMinus half I) = alg.one := by
  rw [← F.map_add, alg.ePlus_add_eMinus half h_half I, F.map_one]

/-- 
  THEOREM: Stabilizer Invariance of the Positive Sheet
  If F preserves I (F I = I), then e₊ is strictly invariant.
-/
theorem map_ePlus_of_fixed (F : NonAssocAlgEnd alg) (half : R) (I : A) (hI : F I = I) :
    F (alg.ePlus half I) = alg.ePlus half I := by
  dsimp [NonAssocUnitalAlgebra.ePlus]
  rw [F.map_smul, F.map_add, F.map_one, hI]

/-- 
  THEOREM: Stabilizer Invariance of the Negative Sheet
  If F preserves I (F I = I), then e₋ is strictly invariant.
-/
theorem map_eMinus_of_fixed (F : NonAssocAlgEnd alg) (half : R) (I : A) (hI : F I = I) :
    F (alg.eMinus half I) = alg.eMinus half I := by
  dsimp [NonAssocUnitalAlgebra.eMinus]
  rw [F.map_smul, F.map_sub, F.map_one, hI]

end NonAssocAlgEnd

end InfoGeometry.Algebra.NonAssocPeirceFrame

end noncomputable section
