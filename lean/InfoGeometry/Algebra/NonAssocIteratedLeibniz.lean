import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset
open BigOperators

namespace InfoGeometry.Algebra.NonAssocIteratedLeibniz

/-!
# Iterated Derivations and Multiplicative Frame Transport

This module owns:
1. The general iterated Leibniz rule for an arbitrary bilinear multiplication (associative or non-associative) using native Mathlib Pascal reindexing (`Finset.sum_choose_succ_nsmul`).
2. Annihilation of any two-sided unit by a derivation (`D one = 0`) and all its positive iterates (`iterD D n one = 0`).
3. Preservation of algebraic relations (idempotents, orthogonalities, square-zero elements) under certified multiplicative linear endomorphisms (`NonAssocAlgEnd`).
4. Stabilizer invariance of positive and negative chiral sheets.
-/

section IteratedLeibniz

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A]
variable (mul : A →ₗ[R] A →ₗ[R] A)

/-- Leibniz rule for the supplied bilinear multiplication. -/
def IsDerivation (D : A →ₗ[R] A) : Prop :=
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
General iterated Leibniz rule, stated with native natural-number scalar
multiplication.

No associativity of `mul` is used anywhere.
-/
theorem iterated_leibniz_nsmul
    (D : A →ₗ[R] A)
    (hD : IsDerivation mul D)
    (n : ℕ) (x y : A) :
    iterD D n (mul x y) =
      ∑ k ∈ range (n + 1),
        n.choose k •
          (mul (iterD D k x) (iterD D (n - k) y)) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_one]
      dsimp [iterD]
      rw [Nat.choose_self, one_nsmul]
  | succ n ih =>
      rw [iterD_succ_apply, ih, map_sum]
      have h_step : ∀ k : ℕ,
          D (n.choose k • (mul (iterD D k x) (iterD D (n - k) y))) =
            n.choose k • (mul (iterD D (k + 1) x) (iterD D (n - k) y)) +
            n.choose k • (mul (iterD D k x) (iterD D (n - k + 1) y)) := by
        intro k
        rw [_root_.map_nsmul, hD, nsmul_add]
        congr 2
        · rw [iterD_succ_apply]
        · rw [iterD_succ_apply]
      simp_rw [h_step]
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

      rw [hsub, add_comm]

      let f : ℕ → ℕ → A :=
        fun i j => mul (iterD D i x) (iterD D j y)

      change (∑ i ∈ range (n + 1), n.choose i • f i (n + 1 - i)) +
             (∑ i ∈ range (n + 1), n.choose i • f (i + 1) (n - i)) =
             ∑ i ∈ range (n + 1 + 1), (n + 1).choose i • f i (n + 1 - i)

      exact (Finset.sum_choose_succ_nsmul f n).symm

/-- Iterated Leibniz with binomial coefficients as ring scalars. -/
theorem iterated_leibniz_smul
    {R : Type*} [CommRing R]
    {A : Type*} [AddCommGroup A] [Module R A]
    (mul : A →ₗ[R] A →ₗ[R] A)
    (D : A →ₗ[R] A)
    (hD : IsDerivation mul D)
    (n : ℕ) (x y : A) :
    iterD D n (mul x y) =
      ∑ k ∈ range (n + 1),
        (n.choose k : R) •
          (mul (iterD D k x) (iterD D (n - k) y)) := by
  simpa only [Nat.cast_smul_eq_nsmul] using
    (iterated_leibniz_nsmul mul D hD n x y)

/-! ## Honest first-order exponential in a square-zero image regime -/

section FirstOrder

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
variable (mul : A →ₗ[R] A →ₗ[R] A)

/-- The truncated exponential `1 + tD` on the underlying module. -/
def firstOrderExp (t : R) (D : A →ₗ[R] A) : A →ₗ[R] A :=
  LinearMap.id + t • D

theorem firstOrderExp_apply
    (t : R) (D : A →ₗ[R] A) (x : A) :
    firstOrderExp t D x = x + t • D x := by
  dsimp [firstOrderExp]

theorem firstOrderExp_map_mul
    (t : R) (D : A →ₗ[R] A)
    (hD : IsDerivation mul D)
    (hDmul : ∀ x y, mul (D x) (D y) = 0)
    (x y : A) :
    firstOrderExp t D (mul x y) =
      mul (firstOrderExp t D x) (firstOrderExp t D y) := by
  rw [firstOrderExp_apply, firstOrderExp_apply, firstOrderExp_apply, hD]
  simp only [mul.map_add, mul.map_smul, LinearMap.map_add,
    LinearMap.map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hDmul, smul_zero, add_zero, smul_add]
  abel

theorem firstOrderExp_map_one
    (t : R) (D : A →ₗ[R] A) (one : A)
    (hD_one : D one = 0) :
    firstOrderExp t D one = one := by
  rw [firstOrderExp_apply, hD_one, smul_zero, add_zero]

/-- The square-zero first-order flow transports both orientations of
orthogonality.  No associativity of `mul` is used. -/
theorem firstOrderExp_map_two_sided_orthogonal
    (t : R) (D : A →ₗ[R] A)
    (hD : IsDerivation mul D)
    (hDmul : ∀ x y, mul (D x) (D y) = 0)
    {e f : A}
    (hef : mul e f = 0)
    (hfe : mul f e = 0) :
    mul (firstOrderExp t D e) (firstOrderExp t D f) = 0 ∧
      mul (firstOrderExp t D f) (firstOrderExp t D e) = 0 := by
  constructor
  · rw [← firstOrderExp_map_mul mul t D hD hDmul e f, hef]
    simp
  · rw [← firstOrderExp_map_mul mul t D hD hDmul f e, hfe]
    simp

/-- The square-zero first-order flow transports idempotents. -/
theorem firstOrderExp_map_idempotent
    (t : R) (D : A →ₗ[R] A)
    (hD : IsDerivation mul D)
    (hDmul : ∀ x y, mul (D x) (D y) = 0)
    {e : A}
    (he : mul e e = e) :
    mul (firstOrderExp t D e) (firstOrderExp t D e) =
      firstOrderExp t D e := by
  rw [← firstOrderExp_map_mul mul t D hD hDmul e e, he]

/-- The square-zero first-order flow transports nilpotent elements of index
two. -/
theorem firstOrderExp_map_square_zero
    (t : R) (D : A →ₗ[R] A)
    (hD : IsDerivation mul D)
    (hDmul : ∀ x y, mul (D x) (D y) = 0)
    {q : A}
    (hq : mul q q = 0) :
    mul (firstOrderExp t D q) (firstOrderExp t D q) = 0 := by
  rw [← firstOrderExp_map_mul mul t D hD hDmul q q, hq]
  simp


/-- A vector fixed by the generator is fixed by the first-order flow. -/
theorem firstOrderExp_fixed_of_derivation_eq_zero
    (t : R) (D : A →ₗ[R] A) (x : A) (hx : D x = 0) :
    firstOrderExp t D x = x := by
  rw [firstOrderExp_apply, hx, smul_zero, add_zero]

theorem firstOrderExp_inverse
    (t : R) (D : A →ₗ[R] A)
    (hD2 : ∀ x, D (D x) = 0)
    (x : A) :
    firstOrderExp (-t) D (firstOrderExp t D x) = x := by
  rw [firstOrderExp_apply, firstOrderExp_apply]
  simp only [map_add, map_smul, hD2, smul_zero, add_zero]
  module

theorem firstOrderExp_inverse'
    (t : R) (D : A →ₗ[R] A)
    (hD2 : ∀ x, D (D x) = 0)
    (x : A) :
    firstOrderExp t D (firstOrderExp (-t) D x) = x := by
  simpa using firstOrderExp_inverse (-t) D hD2 x

/-- The truncated flow has the additive parameter law in the square-zero
image regime. -/
theorem firstOrderExp_add_apply
    (s t : R) (D : A →ₗ[R] A)
    (hD2 : ∀ x, D (D x) = 0)
    (x : A) :
    firstOrderExp (s + t) D x =
      firstOrderExp s D (firstOrderExp t D x) := by
  rw [firstOrderExp_apply, firstOrderExp_apply, firstOrderExp_apply]
  simp only [map_add, map_smul, hD2, smul_zero, add_zero]
  module

end FirstOrder

end IteratedLeibniz

section DerivationBracket

variable {R : Type*} [CommRing R]
variable {A : Type*} [AddCommGroup A] [Module R A]
variable (mul : A →ₗ[R] A →ₗ[R] A)

/-- The commutator of two linear endomorphisms. -/
def derivationCommutator (D E : A →ₗ[R] A) : A →ₗ[R] A :=
  D.comp E - E.comp D

/-- Derivations are closed under the endomorphism commutator, without any
associativity assumption on the underlying multiplication. -/
theorem derivationCommutator_isDerivation
    (D E : A →ₗ[R] A)
    (hD : IsDerivation mul D)
    (hE : IsDerivation mul E) :
    IsDerivation mul (derivationCommutator D E) := by
  intro x y
  simp only [derivationCommutator, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hE x y, D.map_add, hD (E x) y, hD x (E y),
    hD x y, E.map_add, hE (D x) y, hE x (D y)]
  rw [LinearMap.map_sub, LinearMap.map_sub]
  simp
  abel

/-- The commutator of a derivation with itself is zero. -/
theorem derivationCommutator_self (D : A →ₗ[R] A) :
    derivationCommutator D D = 0 := by
  ext x
  simp [derivationCommutator]

/-- Swapping the entries negates the derivation commutator. -/
theorem derivationCommutator_swap (D E : A →ₗ[R] A) :
    derivationCommutator E D = -derivationCommutator D E := by
  ext x
  simp [derivationCommutator, sub_eq_add_neg]

/-- The derivation commutator satisfies the Jacobi identity. -/
theorem derivationCommutator_jacobi (D E F : A →ₗ[R] A) :
    derivationCommutator D (derivationCommutator E F) +
        derivationCommutator E (derivationCommutator F D) +
        derivationCommutator F (derivationCommutator D E) = 0 := by
  ext x
  simp only [derivationCommutator, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.map_sub, LinearMap.zero_apply]
  abel

/-- The derivation commutator is additive in its left entry. -/
theorem derivationCommutator_add_left
    (D₁ D₂ E : A →ₗ[R] A) :
    derivationCommutator (D₁ + D₂) E =
      derivationCommutator D₁ E + derivationCommutator D₂ E := by
  ext x
  simp [derivationCommutator]
  abel

/-- The derivation commutator is additive in its right entry. -/
theorem derivationCommutator_add_right
    (D E₁ E₂ : A →ₗ[R] A) :
    derivationCommutator D (E₁ + E₂) =
      derivationCommutator D E₁ + derivationCommutator D E₂ := by
  ext x
  simp [derivationCommutator]
  abel

/-- The derivation commutator is homogeneous in its left entry. -/
theorem derivationCommutator_smul_left
    (r : R) (D E : A →ₗ[R] A) :
    derivationCommutator (r • D) E = r • derivationCommutator D E := by
  ext x
  simp [derivationCommutator]
  rw [smul_sub]

/-- The derivation commutator is homogeneous in its right entry. -/
theorem derivationCommutator_smul_right
    (r : R) (D E : A →ₗ[R] A) :
    derivationCommutator D (r • E) = r • derivationCommutator D E := by
  ext x
  simp [derivationCommutator]
  rw [smul_sub]

end DerivationBracket

section Unit

variable {R : Type*} [CommRing R]
variable {A : Type*} [AddCommGroup A] [Module R A]
variable (mul : A →ₗ[R] A →ₗ[R] A)

/-- A derivation annihilates any supplied two-sided unit. -/
theorem derivation_kills_one
    (D : A →ₗ[R] A)
    (one : A)
    (h_unit_left : ∀ a : A, mul one a = a)
    (h_unit_right : ∀ a : A, mul a one = a)
    (hD : IsDerivation mul D) :
    D one = 0 := by
  have h : D one = D one + D one := by
    have h_leib := hD one one
    have h_left : mul one one = one := h_unit_left one
    have h_right_done : mul (D one) one = D one := h_unit_right (D one)
    have h_left_done : mul one (D one) = D one := h_unit_left (D one)
    rw [h_left] at h_leib
    rw [h_right_done, h_left_done] at h_leib
    exact h_leib
  have h' : D one + D one = D one + 0 := by
    rw [← h, add_zero]
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

/-- In particular, all positive iterates annihilate the unit. -/
theorem iterD_kills_one
    (D : A →ₗ[R] A)
    (one : A)
    (hD_one : D one = 0)
    (n : ℕ)
    (hn : 0 < n) :
    iterD D n one = 0 :=
  iterD_eq_zero_of_apply_eq_zero D one hD_one n hn

end Unit

/-! ## Certified multiplicative transport -/

section Transport

variable {R : Type*} [CommRing R]
variable {A : Type*} [AddCommGroup A] [Module R A]
variable (mul : A →ₗ[R] A →ₗ[R] A)
variable (one : A)

/--
A unital multiplicative linear endomorphism of a potentially nonassociative
algebra.

This is the exact structure required by the frame-transport theorems.
-/
structure NonAssocAlgEnd where
  toLinearMap : A →ₗ[R] A

  map_mul' :
    ∀ x y : A,
      toLinearMap (mul x y) =
        mul (toLinearMap x) (toLinearMap y)

  map_one' :
    toLinearMap one = one

namespace NonAssocAlgEnd

instance : CoeFun (NonAssocAlgEnd mul one) (fun _ => A → A) where
  coe F := F.toLinearMap

variable {mul one}

@[simp] theorem map_mul
    (F : NonAssocAlgEnd mul one)
    (x y : A) :
    F (mul x y) = mul (F x) (F y) :=
  F.map_mul' x y

@[simp] theorem map_one
    (F : NonAssocAlgEnd mul one) :
    F one = one :=
  F.map_one'

@[simp] theorem map_zero
    (F : NonAssocAlgEnd mul one) :
    F 0 = 0 :=
  F.toLinearMap.map_zero

/-- Multiplicative maps preserve idempotents. -/
theorem map_idempotent
    (F : NonAssocAlgEnd mul one)
    {e : A}
    (he : mul e e = e) :
    mul (F e) (F e) = F e := by
  rw [← F.map_mul, he]

/-- Multiplicative maps preserve an oriented orthogonality relation. -/
theorem map_orthogonal
    (F : NonAssocAlgEnd mul one)
    {e f : A}
    (hef : mul e f = 0) :
    mul (F e) (F f) = 0 := by
  rw [← F.map_mul, hef, F.map_zero]

/-- Multiplicative maps preserve the reverse orientation of orthogonality. -/
theorem map_orthogonal_rev
    (F : NonAssocAlgEnd mul one)
    {e f : A}
    (hfe : mul f e = 0) :
    mul (F f) (F e) = 0 := by
  rw [← F.map_mul, hfe, F.map_zero]

/-- Multiplicative maps preserve two-sided orthogonality. -/
theorem map_two_sided_orthogonal
    (F : NonAssocAlgEnd mul one)
    {e f : A}
    (hef : mul e f = 0)
    (hfe : mul f e = 0) :
    mul (F e) (F f) = 0 ∧ mul (F f) (F e) = 0 := by
  exact ⟨F.map_orthogonal hef, F.map_orthogonal_rev hfe⟩

/-- Multiplicative maps preserve square-zero elements. -/
theorem map_square_zero
    (F : NonAssocAlgEnd mul one)
    {q : A}
    (hq : mul q q = 0) :
    mul (F q) (F q) = 0 := by
  rw [← F.map_mul, hq, F.map_zero]

end NonAssocAlgEnd

/--
Peirce coordinates with an explicit half-scalar.

Using an explicit `half` keeps this definition valid over a general
commutative ring. A concrete owner may supply `half = ⅟ (2 : R)`.
-/
def ePlus (half : R) (I : A) : A :=
  half • (one + I)

def eMinus (half : R) (I : A) : A :=
  half • (one - I)

theorem map_ePlus_of_fixed
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

theorem map_eMinus_of_fixed
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

/-! ## Explicit multiplicative equivalences -/

section Equiv

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
variable (mul : A →ₗ[R] A →ₗ[R] A) (one : A)

/-- A multiplicative linear equivalence for a possibly nonassociative product. -/
structure NonAssocAlgEquiv where
  toLinearMap : A →ₗ[R] A
  invFun : A → A
  map_mul' : ∀ x y, toLinearMap (mul x y) = mul (toLinearMap x) (toLinearMap y)
  map_one' : toLinearMap one = one
  left_inv' : ∀ x, invFun (toLinearMap x) = x
  right_inv' : ∀ x, toLinearMap (invFun x) = x

namespace NonAssocAlgEquiv

instance : CoeFun (NonAssocAlgEquiv mul one) (fun _ => A → A) where
  coe F := F.toLinearMap

@[simp] theorem map_mul
    (F : NonAssocAlgEquiv mul one) (x y : A) :
    F (mul x y) = mul (F x) (F y) := F.map_mul' x y

@[simp] theorem map_one
    (F : NonAssocAlgEquiv mul one) :
    F one = one := F.map_one'

@[simp] theorem map_zero
    (F : NonAssocAlgEquiv mul one) :
    F 0 = 0 := F.toLinearMap.map_zero

@[simp] theorem map_add
    (F : NonAssocAlgEquiv mul one) (x y : A) :
    F (x + y) = F x + F y := F.toLinearMap.map_add x y

@[simp] theorem map_smul
    (F : NonAssocAlgEquiv mul one) (r : R) (x : A) :
    F (r • x) = r • F x := F.toLinearMap.map_smul r x

theorem left_inv
    (F : NonAssocAlgEquiv mul one) (x : A) :
    F.invFun (F x) = x := F.left_inv' x

theorem right_inv
    (F : NonAssocAlgEquiv mul one) (x : A) :
    F (F.invFun x) = x := F.right_inv' x

theorem injective
    (F : NonAssocAlgEquiv mul one) :
    Function.Injective F := by
  intro x y h
  rw [← F.left_inv' x, ← F.left_inv' y, h]

theorem invFun_map_mul
    (F : NonAssocAlgEquiv mul one) (x y : A) :
    F.invFun (mul x y) = mul (F.invFun x) (F.invFun y) := by
  apply F.injective
  simp only [F.right_inv', F.map_mul]

theorem invFun_map_one
    (F : NonAssocAlgEquiv mul one) :
    F.invFun one = one := by
  apply F.injective
  simp only [F.right_inv', F.map_one]

@[simp] theorem invFun_map_zero
    (F : NonAssocAlgEquiv mul one) :
    F.invFun 0 = 0 := by
  apply F.injective
  simp only [F.right_inv', F.map_zero]

theorem invFun_map_orthogonal
    (F : NonAssocAlgEquiv mul one) {e f : A}
    (hef : mul e f = 0) :
    mul (F.invFun e) (F.invFun f) = 0 := by
  rw [← F.invFun_map_mul, hef, F.invFun_map_zero]

theorem invFun_map_orthogonal_rev
    (F : NonAssocAlgEquiv mul one) {e f : A}
    (hfe : mul f e = 0) :
    mul (F.invFun f) (F.invFun e) = 0 := by
  rw [← F.invFun_map_mul, hfe, F.invFun_map_zero]

theorem invFun_map_two_sided_orthogonal
    (F : NonAssocAlgEquiv mul one) {e f : A}
    (hef : mul e f = 0) (hfe : mul f e = 0) :
    mul (F.invFun e) (F.invFun f) = 0 ∧
      mul (F.invFun f) (F.invFun e) = 0 := by
  exact ⟨invFun_map_orthogonal (mul := mul) (one := one) F hef,
    invFun_map_orthogonal_rev (mul := mul) (one := one) F hfe⟩

theorem map_idempotent
    (F : NonAssocAlgEquiv mul one) {e : A}
    (he : mul e e = e) :
    mul (F e) (F e) = F e := by
  rw [← F.map_mul, he]

theorem invFun_map_idempotent
    (F : NonAssocAlgEquiv mul one) {e : A}
    (he : mul e e = e) :
    mul (F.invFun e) (F.invFun e) = F.invFun e := by
  rw [← F.invFun_map_mul, he]

theorem map_orthogonal
    (F : NonAssocAlgEquiv mul one) {e f : A}
    (hef : mul e f = 0) :
    mul (F e) (F f) = 0 := by
  rw [← F.map_mul, hef, F.map_zero]

theorem map_orthogonal_rev
    (F : NonAssocAlgEquiv mul one) {e f : A}
    (hfe : mul f e = 0) :
    mul (F f) (F e) = 0 := by
  rw [← F.map_mul, hfe, F.map_zero]

theorem map_two_sided_orthogonal
    (F : NonAssocAlgEquiv mul one) {e f : A}
    (hef : mul e f = 0) (hfe : mul f e = 0) :
    mul (F e) (F f) = 0 ∧ mul (F f) (F e) = 0 := by
  constructor
  · rw [← F.map_mul, hef, F.map_zero]
  · rw [← F.map_mul, hfe, F.map_zero]

theorem map_square_zero
    (F : NonAssocAlgEquiv mul one) {q : A}
    (hq : mul q q = 0) :
    mul (F q) (F q) = 0 := by
  rw [← F.map_mul, hq, F.map_zero]

theorem invFun_map_square_zero
    (F : NonAssocAlgEquiv mul one) {q : A}
    (hq : mul q q = 0) :
    mul (F.invFun q) (F.invFun q) = 0 := by
  rw [← F.invFun_map_mul, hq, F.invFun_map_zero]

end NonAssocAlgEquiv

end Equiv

end Transport

end InfoGeometry.Algebra.NonAssocIteratedLeibniz
