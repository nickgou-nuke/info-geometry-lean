import Mathlib.Algebra.Module.LinearMap.End
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import InfoGeometry.Algebra.AlternativeDerivations

/-!
# Iterated nonassociative derivations and frame transport

This file complements the repository's native `NonAssocDerivation` owner.
It proves:

* the general iterated Leibniz formula without associativity;
* annihilation of a supplied two-sided unit;
* annihilation by every positive iterate;
* preservation of idempotents, both oriented orthogonality laws, and
  square-zero elements by a certified multiplicative linear equivalence;
* transport of a complete two-idempotent Peirce frame.

No general exponential of a derivation is postulated here.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace InfoGeometry.Algebra.NonAssocIteratedLeibnizTransport

universe u v

variable {R : Type u} {A : Type v}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-! ## Iterated Leibniz rule -/

/-- `n`-fold iteration of the underlying linear endomorphism. -/
def iterD (D : NonAssocDerivation R A) (n : ℕ) : A →ₗ[R] A :=
  D.toLinearMap ^ n

@[simp] theorem iterD_zero (D : NonAssocDerivation R A) :
    iterD D 0 = LinearMap.id :=
  rfl

/-- Successor iteration with `D` as the outer map. -/
@[simp] theorem iterD_succ (D : NonAssocDerivation R A) (n : ℕ) :
    iterD D (n + 1) = D.toLinearMap.comp (iterD D n) := by
  change D.toLinearMap ^ (n + 1) =
    D.toLinearMap.comp (D.toLinearMap ^ n)
  exact Module.End.iterate_succ' (f' := D.toLinearMap) n

@[simp] theorem iterD_succ_apply
    (D : NonAssocDerivation R A) (n : ℕ) (x : A) :
    iterD D (n + 1) x = D (iterD D n x) := by
  rw [iterD_succ, LinearMap.comp_apply]
  rfl

/--
General iterated Leibniz formula.

No associativity of multiplication is used.
-/
theorem iterated_leibniz
    (D : NonAssocDerivation R A)
    (n : ℕ) (x y : A) :
    iterD D n (x * y) =
      ∑ k ∈ range (n + 1),
        n.choose k • (iterD D k x * iterD D (n - k) y) := by
  induction n with
  | zero =>
      simp [iterD]
  | succ n ih =>
      rw [iterD_succ_apply]
      change D.toLinearMap (iterD D n (x * y)) = _
      rw [ih, map_sum]
      simp_rw [map_nsmul, NonAssocDerivation.toLinearMap_apply,
        NonAssocDerivation.leibniz]
      simp_rw [← iterD_succ_apply, nsmul_add]
      rw [sum_add_distrib]
      have hsecond :
          (∑ k ∈ range (n + 1),
              n.choose k •
                (iterD D k x * iterD D (n - k + 1) y)) =
            ∑ k ∈ range (n + 1),
              n.choose k •
                (iterD D k x * iterD D (n + 1 - k) y) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk_le : k ≤ n := by
          exact Nat.le_of_lt_succ (mem_range.mp hk)
        have hindex : n - k + 1 = n + 1 - k := by
          omega
        rw [hindex]
      rw [hsecond]
      rw [add_comm]
      exact (sum_choose_succ_nsmul (fun i j => iterD D i x * iterD D j y) n).symm

/-! ## Unit annihilation -/

/-- A derivation annihilates any supplied two-sided unit. -/
theorem derivation_kills_unit
    (D : NonAssocDerivation R A)
    (one : A)
    (unit_mul : ∀ a : A, one * a = a)
    (mul_unit : ∀ a : A, a * one = a) :
    D one = 0 := by
  have h1 : D one = D one + D one := by
    have h := D.leibniz one one
    simp only [unit_mul, mul_unit] at h
    exact h
  have h2 : D one + 0 = D one + D one := by
    rw [add_zero]
    exact h1
  exact (add_left_cancel h2).symm

/-- A derivation kills every scalar multiple of a supplied two-sided unit. -/
theorem derivation_kills_scalar_unit
    (D : NonAssocDerivation R A)
    (one : A)
    (unit_mul : ∀ a : A, one * a = a)
    (mul_unit : ∀ a : A, a * one = a)
    (c : R) :
    D (c • one) = 0 := by
  rw [D.map_smul]
  rw [derivation_kills_unit D one unit_mul mul_unit]
  simp

/-- Scalar multiples of the supplied unit lie in the derivation kernel. -/
theorem scalar_unit_mem_derivation_ker
    (D : NonAssocDerivation R A)
    (one : A)
    (unit_mul : ∀ a : A, one * a = a)
    (mul_unit : ∀ a : A, a * one = a)
    (c : R) :
    c • one ∈ D.toLinearMap.ker := by
  exact derivation_kills_scalar_unit D one unit_mul mul_unit c

/-- Equality after a derivation is equality modulo its linear kernel. -/
theorem derivation_eq_iff_sub_mem_kernel
    (D : NonAssocDerivation R A) (x y : A) :
    D x = D y ↔ x - y ∈ D.toLinearMap.ker := by
  change D x = D y ↔ D.toLinearMap (x - y) = 0
  rw [D.toLinearMap.map_sub]
  exact (sub_eq_zero).symm

/-- Every positive iterate annihilates a vector already annihilated by `D`. -/
theorem iterD_eq_zero_of_apply_eq_zero
    (D : NonAssocDerivation R A)
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

/-- All positive iterates annihilate a supplied unit. -/
theorem iterD_kills_unit
    (D : NonAssocDerivation R A)
    (one : A)
    (unit_mul : ∀ a : A, one * a = a)
    (mul_unit : ∀ a : A, a * one = a)
    (n : ℕ)
    (hn : 0 < n) :
    iterD D n one = 0 :=
  iterD_eq_zero_of_apply_eq_zero D one
    (derivation_kills_unit D one unit_mul mul_unit) n hn

/-! ## Certified multiplicative linear equivalences -/

/--
A linear equivalence preserving a supplied nonassociative multiplication and
unit element.
-/
structure NonAssocAlgEquiv (one : A) where
  toLinearEquiv : A ≃ₗ[R] A
  map_mul' : ∀ x y : A,
    toLinearEquiv (x * y) = toLinearEquiv x * toLinearEquiv y
  map_one' : toLinearEquiv one = one

namespace NonAssocAlgEquiv

variable {one : A}

instance : CoeFun (NonAssocAlgEquiv (R := R) one) (fun _ => A → A) where
  coe F := F.toLinearEquiv

@[simp] theorem map_mul
    (F : NonAssocAlgEquiv (R := R) one) (x y : A) :
    F (x * y) = F x * F y :=
  F.map_mul' x y

@[simp] theorem map_one
    (F : NonAssocAlgEquiv (R := R) one) :
    F one = one :=
  F.map_one'

@[simp] theorem map_zero
    (F : NonAssocAlgEquiv (R := R) one) :
    F 0 = 0 :=
  F.toLinearEquiv.map_zero

/-- The inverse linear equivalence is multiplicative. -/
theorem symm_map_mul
    (F : NonAssocAlgEquiv (R := R) one) (x y : A) :
    F.toLinearEquiv.symm (x * y) =
      F.toLinearEquiv.symm x * F.toLinearEquiv.symm y := by
  apply F.toLinearEquiv.injective
  rw [F.toLinearEquiv.apply_symm_apply]
  rw [F.map_mul]
  rw [F.toLinearEquiv.apply_symm_apply, F.toLinearEquiv.apply_symm_apply]

/-- The inverse linear equivalence fixes the supplied unit. -/
theorem symm_map_one
    (F : NonAssocAlgEquiv (R := R) one) :
    F.toLinearEquiv.symm one = one := by
  apply F.toLinearEquiv.injective
  rw [F.toLinearEquiv.apply_symm_apply, F.map_one]

/-- Multiplicative equivalences preserve idempotents. -/
theorem map_idempotent
    (F : NonAssocAlgEquiv (R := R) one)
    {e : A} (he : e * e = e) :
    F e * F e = F e := by
  rw [← F.map_mul, he]

/-- Multiplicative equivalences preserve an oriented zero-product relation. -/
theorem map_zero_product
    (F : NonAssocAlgEquiv (R := R) one)
    {e f : A} (hef : e * f = 0) :
    F e * F f = 0 := by
  rw [← F.map_mul, hef, F.map_zero]

/-- Multiplicative equivalences preserve square-zero elements. -/
theorem map_square_zero
    (F : NonAssocAlgEquiv (R := R) one)
    {q : A} (hq : q * q = 0) :
    F q * F q = 0 := by
  exact F.map_zero_product hq

end NonAssocAlgEquiv

/-! ## Complete Peirce-frame transport -/

/-- A complete ordered pair of complementary orthogonal idempotents. -/
structure PeirceFrame (one : A) where
  plus : A
  minus : A
  plus_idempotent : plus * plus = plus
  minus_idempotent : minus * minus = minus
  plus_mul_minus : plus * minus = 0
  minus_mul_plus : minus * plus = 0
  add_eq_one : plus + minus = one

namespace PeirceFrame

variable {one : A}

/-- Transport a complete Peirce frame through a multiplicative equivalence. -/
def transport
    (P : PeirceFrame one)
    (F : NonAssocAlgEquiv (R := R) one) :
    PeirceFrame one where
  plus := F P.plus
  minus := F P.minus
  plus_idempotent := F.map_idempotent P.plus_idempotent
  minus_idempotent := F.map_idempotent P.minus_idempotent
  plus_mul_minus := F.map_zero_product P.plus_mul_minus
  minus_mul_plus := F.map_zero_product P.minus_mul_plus
  add_eq_one := by
    calc
      F P.plus + F P.minus = F (P.plus + P.minus) :=
        (F.toLinearEquiv.map_add P.plus P.minus).symm
      _ = F one := by rw [P.add_eq_one]
      _ = one := F.map_one

@[simp] theorem transport_plus
    (P : PeirceFrame one)
    (F : NonAssocAlgEquiv (R := R) one) :
    (P.transport F).plus = F P.plus :=
  rfl

@[simp] theorem transport_minus
    (P : PeirceFrame one)
    (F : NonAssocAlgEquiv (R := R) one) :
    (P.transport F).minus = F P.minus :=
  rfl

end PeirceFrame

/-! ## Algebraic split-idempotent coordinates -/

/-- Algebraic `e₊ = half • (1 + I)`. -/
def ePlus (one : A) (half : R) (I : A) : A :=
  half • (one + I)

/-- Algebraic `e₋ = half • (1 - I)`. -/
def eMinus (one : A) (half : R) (I : A) : A :=
  half • (one - I)

private theorem smul_mul_smul
    (r s : R) (x y : A) :
    (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/--
Construct the complete split Peirce frame from a two-sided unit, an involution
`I * I = one`, and an explicit half-scalar satisfying `2 * half = 1`.
-/
def splitPeirceFrame
    (one : A)
    (unit_mul : ∀ a : A, one * a = a)
    (mul_unit : ∀ a : A, a * one = a)
    (half : R)
    (half_spec : (2 : R) * half = 1)
    (I : A)
    (I_sq : I * I = one) :
    PeirceFrame one := by
  have htwo : half + half = 1 := by
    simpa [two_mul] using half_spec
  have hcoeff : half * half + half * half = half := by
    calc
      half * half + half * half = (half + half) * half := by ring
      _ = 1 * half := by rw [htwo]
      _ = half := one_mul half
  have hplus_prod : (one + I) * (one + I) = (one + I) + (one + I) := by
    rw [add_mul, mul_add, mul_add]
    simp only [unit_mul, mul_unit, I_sq]
    abel
  have hminus_prod : (one - I) * (one - I) = (one - I) + (one - I) := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [unit_mul, mul_unit, I_sq]
    abel
  have hplus_minus : (one + I) * (one - I) = 0 := by
    rw [add_mul, mul_sub, mul_sub]
    simp only [unit_mul, mul_unit, I_sq]
    abel
  have hminus_plus : (one - I) * (one + I) = 0 := by
    rw [sub_mul, mul_add, mul_add]
    simp only [unit_mul, mul_unit, I_sq]
    abel
  refine
    { plus := ePlus one half I
      minus := eMinus one half I
      plus_idempotent := ?_
      minus_idempotent := ?_
      plus_mul_minus := ?_
      minus_mul_plus := ?_
      add_eq_one := ?_ }
  · unfold ePlus
    rw [smul_mul_smul, hplus_prod, smul_add, ← add_smul, hcoeff]
  · unfold eMinus
    rw [smul_mul_smul, hminus_prod, smul_add, ← add_smul, hcoeff]
  · unfold ePlus eMinus
    rw [smul_mul_smul, hplus_minus, smul_zero]
  · unfold ePlus eMinus
    rw [smul_mul_smul, hminus_plus, smul_zero]
  · unfold ePlus eMinus
    rw [← smul_add]
    have hsum : (one + I) + (one - I) = one + one := by
      abel
    rw [hsum, smul_add, ← add_smul, htwo, one_smul]

/-- A multiplicative equivalence fixing `I` fixes `e₊`. -/
theorem map_ePlus_of_fixed
    {one : A}
    (F : NonAssocAlgEquiv (R := R) one)
    (half : R) (I : A)
    (hI : F I = I) :
    F (ePlus one half I) = ePlus one half I := by
  unfold ePlus
  have h1 : F.toLinearEquiv (one + I) = F.toLinearEquiv one + F.toLinearEquiv I :=
    map_add F.toLinearEquiv one I
  show F.toLinearEquiv (half • (one + I)) = half • (one + I)
  rw [map_smul, h1, F.map_one, hI]

/-- A multiplicative equivalence fixing `I` fixes `e₋`. -/
theorem map_eMinus_of_fixed
    {one : A}
    (F : NonAssocAlgEquiv (R := R) one)
    (half : R) (I : A)
    (hI : F I = I) :
    F (eMinus one half I) = eMinus one half I := by
  unfold eMinus
  have h1 : F.toLinearEquiv (one - I) = F.toLinearEquiv one - F.toLinearEquiv I :=
    map_sub F.toLinearEquiv one I
  show F.toLinearEquiv (half • (one - I)) = half • (one - I)
  rw [map_smul, h1, F.map_one, hI]

end InfoGeometry.Algebra.NonAssocIteratedLeibnizTransport

end noncomputable section
