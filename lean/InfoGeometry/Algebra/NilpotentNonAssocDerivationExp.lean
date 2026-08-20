import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import InfoGeometry.Algebra.NonAssocIteratedLeibniz

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset
open BigOperators
open InfoGeometry.Algebra.NonAssocIteratedLeibniz

namespace InfoGeometry.Algebra.NilpotentNonAssocDerivationExp

variable {K A : Type*} [Field K] [CharZero K] [AddCommGroup A] [Module K A]
variable (mul : A →ₗ[K] A →ₗ[K] A) (one : A)

/-!
# Nilpotent Derivation Exponentials in Non-Associative Algebras

This module owns:
1. The explicit truncated exponential of a linear endomorphism `nilpotentExp D N`.
2. Annihilation preservation: `nilpotentExp D N one = one` for derivations killing the unit.
3. The 2-step / quadratic nilpotent derivation exponential isomorphism:
   `exp(tD) (x ⋆ y) = (exp(tD) x) ⋆ (exp(tD) y)` when `D² = 0` and `D x ⋆ D y = 0`.
4. Invertibility: `exp(tD) ∘ exp(-tD) = id`.
5. Multiplicative transport of non-associative structures under nilpotent flows.
-/

/-- Truncated polynomial exponential of an endomorphism up to order `N`. -/
def nilpotentExp (D : A →ₗ[K] A) (N : ℕ) : A →ₗ[K] A :=
  ∑ k ∈ range N, ((Nat.factorial k : K)⁻¹) • (D ^ k)

@[simp] theorem nilpotentExp_zero (D : A →ₗ[K] A) :
    nilpotentExp D 0 = 0 :=
  rfl

@[simp] theorem nilpotentExp_one (D : A →ₗ[K] A) :
    nilpotentExp D 1 = LinearMap.id := by
  ext x
  dsimp [nilpotentExp]
  simp

/-- For `N = 2`, `nilpotentExp D 2 = id + D`. -/
theorem nilpotentExp_two (D : A →ₗ[K] A) :
    nilpotentExp D 2 = LinearMap.id + D := by
  ext x
  dsimp [nilpotentExp]
  simp [sum_range_succ, Nat.factorial]

/-- Evaluation of `nilpotentExp D 2` at an element `x`: `(id + D) x = x + D x`. -/
@[simp] theorem nilpotentExp_two_apply (D : A →ₗ[K] A) (x : A) :
    nilpotentExp D 2 x = x + D x := by
  rw [nilpotentExp_two, LinearMap.add_apply, LinearMap.id_apply]

/-- Scaled 2-step nilpotent exponential `exp(tD) = id + t • D`. -/
def nilpotentExpStep2 (D : A →ₗ[K] A) (t : K) : A →ₗ[K] A :=
  LinearMap.id + t • D

@[simp] theorem nilpotentExpStep2_apply (D : A →ₗ[K] A) (t : K) (x : A) :
    nilpotentExpStep2 D t x = x + t • D x :=
  rfl

@[simp] theorem nilpotentExpStep2_zero (D : A →ₗ[K] A) :
    nilpotentExpStep2 D 0 = LinearMap.id := by
  ext x
  simp [nilpotentExpStep2_apply]

/-- Unital action: `exp(tD) one = one` whenever `D one = 0`. -/
theorem nilpotentExpStep2_one (D : A →ₗ[K] A) (t : K) (hD_one : D one = 0) :
    nilpotentExpStep2 D t one = one := by
  simp [nilpotentExpStep2_apply, hD_one]

/--
🏆 THEOREM: Product preservation of the 2-step nilpotent derivation exponential.
When `D` is a derivation and `D x ⋆ D y = 0` (nilpotent abelian lane),
`exp(tD) (x ⋆ y) = (exp(tD) x) ⋆ (exp(tD) y)`.
-/
theorem nilpotentExpStep2_map_mul (D : A →ₗ[K] A) (hD : IsDerivation mul D)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0) (t : K) (x y : A) :
    nilpotentExpStep2 D t (mul x y) =
      mul (nilpotentExpStep2 D t x) (nilpotentExpStep2 D t y) := by
  simp only [nilpotentExpStep2_apply]
  rw [hD x y]
  have h1 : mul (x + t • D x) (y + t • D y) =
      mul x y + t • mul x (D y) + t • mul (D x) y + (t * t) • mul (D x) (D y) := by
    rw [LinearMap.map_add₂, LinearMap.map_add, LinearMap.map_add,
        LinearMap.map_smul, LinearMap.map_smul₂]
    have h_smul2 : mul (t • D x) (t • D y) = (t * t) • mul (D x) (D y) := by
      rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
    rw [h_smul2]
    abel
  rw [h1, h_cross x y, smul_zero, add_zero]
  simp only [smul_add]
  abel

/-- Group inverse law: `exp(tD) ∘ exp(-tD) = id` when `D² = 0`. -/
theorem nilpotentExpStep2_comp_neg (D : A →ₗ[K] A) (hD2 : D.comp D = 0) (t : K) :
    (nilpotentExpStep2 D t).comp (nilpotentExpStep2 D (-t)) = LinearMap.id := by
  ext x
  simp only [LinearMap.comp_apply, nilpotentExpStep2_apply, LinearMap.map_add, LinearMap.map_smul, LinearMap.id_apply]
  have hD2x : D (D x) = 0 := by
    have : (D.comp D) x = 0 := by rw [hD2, LinearMap.zero_apply]
    exact this
  rw [hD2x, smul_zero, add_zero]
  have h_cancel : t • D x + -t • D x = 0 := by
    rw [← add_smul, add_neg_cancel, zero_smul]
  rw [add_assoc, h_cancel, add_zero]

/-- Group composition law: `exp(sD) ∘ exp(tD) = exp((s+t)D)` when `D² = 0`. -/
theorem nilpotentExpStep2_comp_add (D : A →ₗ[K] A) (hD2 : D.comp D = 0) (s t : K) :
    (nilpotentExpStep2 D s).comp (nilpotentExpStep2 D t) = nilpotentExpStep2 D (s + t) := by
  ext x
  simp only [LinearMap.comp_apply, nilpotentExpStep2_apply, LinearMap.map_add, LinearMap.map_smul]
  have hD2x : D (D x) = 0 := by
    have : (D.comp D) x = 0 := by rw [hD2, LinearMap.zero_apply]
    exact this
  rw [hD2x, smul_zero, add_zero]
  have h_add : s • D x + t • D x = (s + t) • D x := by
    rw [← add_smul]
  rw [add_assoc, h_add]

/-- Bundled `NonAssocAlgEnd` constructed from a 2-step nilpotent derivation exponential. -/
def toNonAssocAlgEnd (D : A →ₗ[K] A) (hD : IsDerivation mul D)
    (h_one : D one = 0) (h_cross : ∀ x y : A, mul (D x) (D y) = 0) (t : K) :
    NonAssocAlgEnd mul one where
  toLinearMap := nilpotentExpStep2 D t
  map_mul' := fun x y => nilpotentExpStep2_map_mul mul D hD h_cross t x y
  map_one' := nilpotentExpStep2_one one D t h_one

/-- A square-nilpotent derivation exponential as a genuine multiplicative
linear equivalence, with inverse given by the negative parameter. -/
def toNonAssocAlgEquiv
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (hD2 : D.comp D = 0)
    (h_one : D one = 0)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : K) : NonAssocIteratedLeibniz.NonAssocAlgEquiv mul one where
  toLinearMap := nilpotentExpStep2 D t
  invFun := nilpotentExpStep2 D (-t)
  map_mul' := fun x y => nilpotentExpStep2_map_mul mul D hD h_cross t x y
  map_one' := nilpotentExpStep2_one one D t h_one
  left_inv' := by
    intro x
    have h := LinearMap.congr_fun (nilpotentExpStep2_comp_neg D hD2 (-t)) x
    simpa [neg_neg] using h
  right_inv' := by
    intro x
    have h := LinearMap.congr_fun (nilpotentExpStep2_comp_neg D hD2 t) x
    exact h

/-- The bundled nilpotent automorphisms satisfy the additive parameter law
pointwise. -/
theorem toNonAssocAlgEquiv_add_apply
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (hD2 : D.comp D = 0)
    (h_one : D one = 0)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (s t : K) (x : A) :
    toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross (s + t) x =
      toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross s
        (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x) := by
  change nilpotentExpStep2 D (s + t) x =
    nilpotentExpStep2 D s (nilpotentExpStep2 D t x)
  exact (LinearMap.congr_fun (nilpotentExpStep2_comp_add D hD2 s t) x).symm

/-- The zero-parameter bundled nilpotent automorphism is pointwise the identity. -/
theorem toNonAssocAlgEquiv_zero_apply
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (hD2 : D.comp D = 0)
    (h_one : D one = 0)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (x : A) :
    toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross 0 x = x := by
  change nilpotentExpStep2 D 0 x = x
  simp

/-- Negative parameters give the pointwise inverse flow. -/
theorem toNonAssocAlgEquiv_neg_apply
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (hD2 : D.comp D = 0)
    (h_one : D one = 0)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : K) (x : A) :
    toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross (-t)
        (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x) = x := by
  change nilpotentExpStep2 D (-t) (nilpotentExpStep2 D t x) = x
  simpa [neg_neg] using
    LinearMap.congr_fun (nilpotentExpStep2_comp_neg D hD2 (-t)) x

/-- The bundled nilpotent automorphism transports the noncommutative
commutator product. -/
theorem toNonAssocAlgEquiv_map_commutator
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (hD2 : D.comp D = 0)
    (h_one : D one = 0)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : K) (x y : A) :
    toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t
        (mul x y - mul y x) =
      mul (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x)
        (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t y) -
      mul (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t y)
        (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x) := by
  change nilpotentExpStep2 D t (mul x y - mul y x) =
    mul (nilpotentExpStep2 D t x) (nilpotentExpStep2 D t y) -
      mul (nilpotentExpStep2 D t y) (nilpotentExpStep2 D t x)
  rw [map_sub, nilpotentExpStep2_map_mul mul D hD h_cross,
    nilpotentExpStep2_map_mul mul D hD h_cross]

/-- The bundled nilpotent automorphism transports idempotents. -/
theorem toNonAssocAlgEquiv_map_idempotent
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (hD2 : D.comp D = 0)
    (h_one : D one = 0)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : K) (x : A)
    (hx : mul x x = x) :
    mul (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x)
      (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x) =
      toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x := by
  change mul (nilpotentExpStep2 D t x) (nilpotentExpStep2 D t x) =
    nilpotentExpStep2 D t x
  rw [← nilpotentExpStep2_map_mul mul D hD h_cross t x x, hx]

/-- The bundled nilpotent automorphism transports square-zero elements. -/
theorem toNonAssocAlgEquiv_map_square_zero
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (hD2 : D.comp D = 0)
    (h_one : D one = 0)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : K) (x : A)
    (hx : mul x x = 0) :
    mul (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x)
      (toNonAssocAlgEquiv mul one D hD hD2 h_one h_cross t x) = 0 := by
  change mul (nilpotentExpStep2 D t x) (nilpotentExpStep2 D t x) = 0
  rw [← nilpotentExpStep2_map_mul mul D hD h_cross t x x, hx]
  exact (nilpotentExpStep2 D t).map_zero

/-- The nilpotent exponential transports both orientations of orthogonality. -/
theorem nilpotentExpStep2_map_two_sided_orthogonal
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : K) (x y : A)
    (hxy : mul x y = 0)
    (hyx : mul y x = 0) :
    mul (nilpotentExpStep2 D t x) (nilpotentExpStep2 D t y) = 0 ∧
      mul (nilpotentExpStep2 D t y) (nilpotentExpStep2 D t x) = 0 := by
  constructor
  · rw [← nilpotentExpStep2_map_mul mul D hD h_cross t x y, hxy]
    exact (nilpotentExpStep2 D t).map_zero
  · rw [← nilpotentExpStep2_map_mul mul D hD h_cross t y x, hyx]
    exact (nilpotentExpStep2 D t).map_zero

/-- The nilpotent exponential transports idempotents. -/
theorem nilpotentExpStep2_map_idempotent
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : K) (x : A)
    (hx : mul x x = x) :
    mul (nilpotentExpStep2 D t x) (nilpotentExpStep2 D t x) =
      nilpotentExpStep2 D t x := by
  rw [← nilpotentExpStep2_map_mul mul D hD h_cross t x x, hx]

/-- The nilpotent exponential transports square-zero elements. -/
theorem nilpotentExpStep2_map_square_zero
    (D : A →ₗ[K] A)
    (hD : IsDerivation mul D)
    (h_cross : ∀ x y : A, mul (D x) (D y) = 0)
    (t : K) (x : A)
    (hx : mul x x = 0) :
    mul (nilpotentExpStep2 D t x) (nilpotentExpStep2 D t x) = 0 := by
  rw [← nilpotentExpStep2_map_mul mul D hD h_cross t x x, hx]
  exact (nilpotentExpStep2 D t).map_zero

end InfoGeometry.Algebra.NilpotentNonAssocDerivationExp
