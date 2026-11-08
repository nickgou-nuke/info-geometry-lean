import Mathlib.Algebra.Module.LinearMap.End
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Non-Associative Peirce Frame, Iterated Leibniz, and Multiplicative Transport

This module provides a fully closed, zero-axiom formalization of:
1. Iterated Leibniz rule for arbitrary bilinear, potentially non-associative multiplications:
   `Dⁿ(x ⋆ y) = ∑_{k=0}^n (n choose k) • (Dᵏ(x) ⋆ Dⁿ⁻ᵏ(y))`
2. Annihilation of a two-sided unit element and all its positive iterates: `D(1) = 0`, `Dⁿ(1) = 0`.
3. Primitive Peirce idempotents and their complete algebraic relations:
   - `ePlus ⋆ ePlus = ePlus`
   - `eMinus ⋆ eMinus = eMinus`
   - `ePlus ⋆ eMinus = 0` (left orthogonality)
   - `eMinus ⋆ ePlus = 0` (right orthogonality)
   - `ePlus + eMinus = 1` (resolution of identity)
4. Certified multiplicative transport:
   - Automatic relation preservation under `NonAssocAlgEnd`
   - Invariance of chiral sheets under the stabilizer of `I` (`F I = I → F ePlus = ePlus`)

No associativity of the bilinear multiplication `mul` is assumed anywhere.
All proofs are 100% native Mathlib with zero `sorry`s, zero custom axioms, and zero admits.
-/

noncomputable section

open Finset
open BigOperators

namespace InfoGeometry.Algebra.NonAssocPeirceFrame

/-!
=============================================================================
PART 1: Iterated Leibniz Rule for Non-Associative Multiplications
=============================================================================
-/

section IteratedLeibniz

variable {R A : Type*}
variable [CommSemiring R] [AddCommMonoid A] [Module R A]

/-- Leibniz rule for an arbitrary bilinear multiplication. -/
def IsDerivation (mul : A →ₗ[R] A →ₗ[R] A) (D : A →ₗ[R] A) : Prop :=
  ∀ x y : A,
    D (mul x y) = mul (D x) y + mul x (D y)

/-- The `n`-fold iterate of a linear endomorphism. -/
def iterD (D : A →ₗ[R] A) (n : ℕ) : A →ₗ[R] A :=
  D ^ n

@[simp] theorem iterD_zero (D : A →ₗ[R] A) :
    iterD D 0 = LinearMap.id :=
  rfl

/-- Successor iteration with `D` on the outside. -/
@[simp] theorem iterD_succ (D : A →ₗ[R] A) (n : ℕ) :
    iterD D (n + 1) = D.comp (iterD D n) := by
  change D ^ (n + 1) = D.comp (D ^ n)
  exact Module.End.iterate_succ' (f' := D) n

@[simp] theorem iterD_succ_apply
    (D : A →ₗ[R] A) (n : ℕ) (x : A) :
    iterD D (n + 1) x = D (iterD D n x) := by
  rw [iterD_succ, LinearMap.comp_apply]

/--
🏆 THEOREM 1: General iterated Leibniz rule, stated with native natural-number scalar
multiplication.

No associativity of `mul` is used.
-/
theorem iterated_leibniz_nsmul
    (mul : A →ₗ[R] A →ₗ[R] A)
    (D : A →ₗ[R] A)
    (hD : IsDerivation mul D)
    (n : ℕ) (x y : A) :
    iterD D n (mul x y) =
      ∑ k ∈ range (n + 1),
        n.choose k •
          (mul (iterD D k x) (iterD D (n - k) y)) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_one, tsub_self, iterD_zero,
          LinearMap.id_apply, LinearMap.id_apply, LinearMap.id_apply,
          Nat.choose_self, one_nsmul]
  | succ n ih =>
      rw [iterD_succ_apply, ih, map_sum]
      simp_rw [
        map_nsmul,
        hD _ _,
        ← iterD_succ_apply,
        nsmul_add
      ]
      rw [sum_add_distrib]

      have hsub :
          (∑ k ∈ range (n + 1),
              n.choose k •
                (mul (iterD D k x)
                  (iterD D (n - k + 1) y))) =
            ∑ k ∈ range (n + 1),
              n.choose k •
                (mul (iterD D k x)
                  (iterD D (n + 1 - k) y)) := by
        apply sum_congr rfl
        intro k hk
        have hk_le : k ≤ n :=
          Nat.le_of_lt_succ (mem_range.mp hk)
        have hnk :
            n - k + 1 = n + 1 - k := by
          simpa [Nat.succ_eq_add_one] using
            (Nat.succ_sub hk_le).symm
        rw [hnk]

      rw [hsub]

      let f : ℕ → ℕ → A :=
        fun i j => mul (iterD D i x) (iterD D j y)

      simpa [f, Nat.succ_eq_add_one, add_comm, add_assoc, add_left_comm] using
        (Finset.sum_choose_succ_nsmul f n).symm

end IteratedLeibniz

/-!
=============================================================================
PART 2: Annihilation of Unit and its Higher Iterates
=============================================================================
-/

section Unit

variable {R A : Type*}
variable [CommRing R] [AddCommGroup A] [Module R A]

/-- 🏆 THEOREM 2: A derivation annihilates any supplied two-sided unit. -/
theorem derivation_kills_one
    (mul : A →ₗ[R] A →ₗ[R] A)
    (D : A →ₗ[R] A)
    (one : A)
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (hD : IsDerivation mul D) :
    D one = 0 := by
  have h : D (mul one one) = mul (D one) one + mul one (D one) := hD one one
  have h_left : mul one one = one := h_unit_left one
  have h_d1 : mul (D one) one = D one := h_unit_right (D one)
  have h_d2 : mul one (D one) = D one := h_unit_left (D one)
  rw [h_left, h_d1, h_d2] at h
  have h' : D one + D one = D one + 0 := by rw [add_zero, ← h]
  exact add_left_cancel h'

/-- Every positive iterate annihilates a point already annihilated by `D`. -/
theorem iterD_eq_zero_of_apply_eq_zero
    (D : A →ₗ[R] A)
    (x : A)
    (hx : D x = 0)
    (n : ℕ)
    (hn : 0 < n) :
    iterD D n x = 0 := by
  cases n with
  | zero =>
      omega
  | succ k =>
      simp [iterD, pow_succ, Module.End.mul_apply, hx]

/-- 🏆 THEOREM 3: In particular, all positive iterates annihilate the unit. -/
theorem iterD_kills_one
    (D : A →ₗ[R] A)
    (one : A)
    (hD_one : D one = 0)
    (n : ℕ)
    (hn : 0 < n) :
    iterD D n one = 0 :=
  iterD_eq_zero_of_apply_eq_zero D one hD_one n hn

end Unit

/-!
=============================================================================
PART 3: Certified Multiplicative Frame Transport
=============================================================================
-/

section Transport

variable {R A : Type*}
variable [CommRing R] [AddCommGroup A] [Module R A]

/--
A unital multiplicative linear endomorphism of a potentially nonassociative
algebra.

This is the exact structure required by the frame-transport theorems.
-/
structure NonAssocAlgEnd (mul : A →ₗ[R] A →ₗ[R] A) (one : A) where
  toLinearMap : A →ₗ[R] A
  map_mul' :
    ∀ x y : A,
      toLinearMap (mul x y) =
        mul (toLinearMap x) (toLinearMap y)
  map_one' :
    toLinearMap one = one

namespace NonAssocAlgEnd

instance {mul : A →ₗ[R] A →ₗ[R] A} {one : A} : CoeFun (NonAssocAlgEnd mul one) (fun _ => A → A) where
  coe F := F.toLinearMap

@[simp] theorem map_mul {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (x y : A) :
    F (mul x y) = mul (F x) (F y) :=
  F.map_mul' x y

@[simp] theorem map_one {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one) :
    F one = one :=
  F.map_one'

@[simp] theorem map_zero {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one) :
    F 0 = 0 :=
  F.toLinearMap.map_zero

@[simp] theorem map_add {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (x y : A) :
    F (x + y) = F x + F y :=
  F.toLinearMap.map_add x y

@[simp] theorem map_sub {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (x y : A) :
    F (x - y) = F x - F y :=
  F.toLinearMap.map_sub x y

@[simp] theorem map_smul {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (c : R) (x : A) :
    F (c • x) = c • F x :=
  F.toLinearMap.map_smul c x

/-- 🏆 THEOREM 4: Multiplicative maps preserve idempotents. -/
theorem map_idempotent {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (e : A)
    (he : mul e e = e) :
    mul (F e) (F e) = F e := by
  rw [← F.map_mul, he]

/-- 🏆 THEOREM 5: Multiplicative maps preserve an oriented orthogonality relation. -/
theorem map_orthogonal {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (e f : A)
    (hef : mul e f = 0) :
    mul (F e) (F f) = 0 := by
  rw [← F.map_mul, hef, F.map_zero]

/-- 🏆 THEOREM 6: Multiplicative maps preserve square-zero elements. -/
theorem map_square_zero {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (q : A)
    (hq : mul q q = 0) :
    mul (F q) (F q) = 0 := by
  rw [← F.map_mul, hq, F.map_zero]

end NonAssocAlgEnd

/--
Peirce coordinates with an explicit half-scalar.

Using an explicit `half` keeps this definition valid over a general
commutative ring. A concrete owner may supply `half = ⅟ (2 : R)`.
-/
def ePlus (one : A) (half : R) (I : A) : A :=
  half • (one + I)

def eMinus (one : A) (half : R) (I : A) : A :=
  half • (one - I)

/-- 🏆 THEOREM 7: Resolution of Identity: e₊ + e₋ = 1 -/
theorem ePlus_add_eMinus (one : A) (half : R) (h_half : (2 : R) * half = 1) (I : A) :
    ePlus one half I + eMinus one half I = one := by
  dsimp [ePlus, eMinus]
  rw [← smul_add]
  have h_sum : (one + I) + (one - I) = (2 : R) • one := by
    calc
      (one + I) + (one - I) = (one + one) + (I - I) := by abel
      _ = (2 : R) • one + 0 := by
        simp only [two_smul, sub_self]
      _ = (2 : R) • one := by rw [add_zero]
  rw [h_sum, smul_smul]
  have h_scalar : half * 2 = 1 := by
    rw [mul_comm, h_half]
  rw [h_scalar, one_smul]

/-- 🏆 THEOREM 8: Idempotency of e₊: e₊ ⋆ e₊ = e₊ -/
theorem ePlus_idempotent (mul : A →ₗ[R] A →ₗ[R] A) (one : A) (half : R) (h_half : (2 : R) * half = 1)
    (h_one_left : ∀ a : A, mul one a = a)
    (h_one_right : ∀ a : A, mul a one = a)
    (I : A) (hI : mul I I = one) :
    mul (ePlus one half I) (ePlus one half I) = ePlus one half I := by
  dsimp [ePlus]
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  have h1 : mul (one + I) = mul one + mul I := mul.map_add one I
  have h3 : mul one (one + I) = mul one one + mul one I := (mul one).map_add one I
  have h4 : mul I (one + I) = mul I one + mul I I := (mul I).map_add one I
  have h_prod : mul (one + I) (one + I) = (2 : R) • (one + I) := by
    calc
      mul (one + I) (one + I)
        = (mul one + mul I) (one + I) := by rw [LinearMap.congr_fun h1 (one + I)]
      _ = mul one (one + I) + mul I (one + I) := rfl
      _ = mul one one + mul one I + (mul I one + mul I I) := by rw [h3, h4]
      _ = one + I + (I + one) := by rw [h_one_left, h_one_left, h_one_right, hI]
      _ = (2 : R) • (one + I) := by
        simp only [two_smul, smul_add]
        abel
  rw [h_prod, smul_smul, smul_smul]
  have h_scal : half * half * 2 = half := by
    calc
      half * half * 2 = half * ((2 : R) * half) := by ring
      _ = half * 1 := by rw [h_half]
      _ = half := mul_one half
  rw [h_scal]

/-- 🏆 THEOREM 9: Idempotency of e₋: e₋ ⋆ e₋ = e₋ -/
theorem eMinus_idempotent (mul : A →ₗ[R] A →ₗ[R] A) (one : A) (half : R) (h_half : (2 : R) * half = 1)
    (h_one_left : ∀ a : A, mul one a = a)
    (h_one_right : ∀ a : A, mul a one = a)
    (I : A) (hI : mul I I = one) :
    mul (eMinus one half I) (eMinus one half I) = eMinus one half I := by
  dsimp [eMinus]
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  have h1 : mul (one - I) = mul one - mul I := mul.map_sub one I
  have h3 : mul one (one - I) = mul one one - mul one I := (mul one).map_sub one I
  have h4 : mul I (one - I) = mul I one - mul I I := (mul I).map_sub one I
  have h_prod : mul (one - I) (one - I) = (2 : R) • (one - I) := by
    calc
      mul (one - I) (one - I)
        = (mul one - mul I) (one - I) := by rw [LinearMap.congr_fun h1 (one - I)]
      _ = mul one (one - I) - mul I (one - I) := rfl
      _ = mul one one - mul one I - (mul I one - mul I I) := by rw [h3, h4]
      _ = one - I - (I - one) := by rw [h_one_left, h_one_left, h_one_right, hI]
      _ = (2 : R) • (one - I) := by
        simp only [two_smul, smul_sub]
        abel
  rw [h_prod, smul_smul, smul_smul]
  have h_scal : half * half * 2 = half := by
    calc
      half * half * 2 = half * ((2 : R) * half) := by ring
      _ = half * 1 := by rw [h_half]
      _ = half := mul_one half
  rw [h_scal]

/-- 🏆 THEOREM 10: Left Orthogonality: e₊ ⋆ e₋ = 0 -/
theorem ePlus_mul_eMinus (mul : A →ₗ[R] A →ₗ[R] A) (one : A) (half : R)
    (h_one_left : ∀ a : A, mul one a = a)
    (h_one_right : ∀ a : A, mul a one = a)
    (I : A) (hI : mul I I = one) :
    mul (ePlus one half I) (eMinus one half I) = 0 := by
  dsimp [ePlus, eMinus]
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  have h1 : mul (one + I) = mul one + mul I := mul.map_add one I
  have h3 : mul one (one - I) = mul one one - mul one I := (mul one).map_sub one I
  have h4 : mul I (one - I) = mul I one - mul I I := (mul I).map_sub one I
  have h_prod : mul (one + I) (one - I) = 0 := by
    calc
      mul (one + I) (one - I)
        = (mul one + mul I) (one - I) := by rw [LinearMap.congr_fun h1 (one - I)]
      _ = mul one (one - I) + mul I (one - I) := rfl
      _ = mul one one - mul one I + (mul I one - mul I I) := by rw [h3, h4]
      _ = one - I + (I - one) := by rw [h_one_left, h_one_left, h_one_right, hI]
      _ = 0 := by abel
  rw [h_prod, smul_zero, smul_zero]

/-- 🏆 THEOREM 11: Right Orthogonality: e₋ ⋆ e₊ = 0 -/
theorem eMinus_mul_ePlus (mul : A →ₗ[R] A →ₗ[R] A) (one : A) (half : R)
    (h_one_left : ∀ a : A, mul one a = a)
    (h_one_right : ∀ a : A, mul a one = a)
    (I : A) (hI : mul I I = one) :
    mul (eMinus one half I) (ePlus one half I) = 0 := by
  dsimp [ePlus, eMinus]
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  have h1 : mul (one - I) = mul one - mul I := mul.map_sub one I
  have h3 : mul one (one + I) = mul one one + mul one I := (mul one).map_add one I
  have h4 : mul I (one + I) = mul I one + mul I I := (mul I).map_add one I
  have h_prod : mul (one - I) (one + I) = 0 := by
    calc
      mul (one - I) (one + I)
        = (mul one - mul I) (one + I) := by rw [LinearMap.congr_fun h1 (one + I)]
      _ = mul one (one + I) - mul I (one + I) := rfl
      _ = mul one one + mul one I - (mul I one + mul I I) := by rw [h3, h4]
      _ = one + I - (I + one) := by rw [h_one_left, h_one_left, h_one_right, hI]
      _ = 0 := by abel
  rw [h_prod, smul_zero, smul_zero]

/-- 🏆 THEOREM 12: Stabilizer Invariance of the Positive Sheet: F(I) = I ⟹ F(e₊) = e₊ -/
theorem map_ePlus_of_fixed {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (half : R) (I : A)
    (hI : F I = I) :
    F (ePlus one half I) = ePlus one half I := by
  calc
    F (half • (one + I))
        = half • F (one + I) :=
          F.toLinearMap.map_smul half (one + I)
    _ = half • (F one + F I) := by
          rw [F.toLinearMap.map_add]
    _ = half • (one + I) := by
          rw [F.map_one, hI]

/-- 🏆 THEOREM 13: Stabilizer Invariance of the Negative Sheet: F(I) = I ⟹ F(e₋) = e₋ -/
theorem map_eMinus_of_fixed {mul : A →ₗ[R] A →ₗ[R] A} {one : A}
    (F : NonAssocAlgEnd mul one)
    (half : R) (I : A)
    (hI : F I = I) :
    F (eMinus one half I) = eMinus one half I := by
  calc
    F (half • (one - I))
        = half • F (one - I) :=
          F.toLinearMap.map_smul half (one - I)
    _ = half • (F one - F I) := by
          rw [F.toLinearMap.map_sub]
    _ = half • (one - I) := by
          rw [F.map_one, hI]

end Transport

end InfoGeometry.Algebra.NonAssocPeirceFrame

end noncomputable section
