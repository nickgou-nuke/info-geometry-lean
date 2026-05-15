import Mathlib

/-!
# InfoGeometry.Arithmetic.PrimeBosonFermionGas

Finite algebraic core of the primon / prime gas dictionary.

This file proves the finite boson × signed-fermion cancellation:

`Z_B(S) * Z_F^signed(S) = 1`

where

`Z_B(S) = ∏ p ∈ S, (1 - x p)⁻¹`

and

`Z_F^signed(S) = ∏ p ∈ S, (1 - x p)`.

No infinite Euler product, zeta theorem, analytic continuation, RH claim,
or cohomology theorem is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeBosonFermionGas

/-! ## 1. Prime-sector carriers -/

/--
A square-free fermionic prime state is a finite set of prime labels.

The label type can later be instantiated by actual primes, but this finite
algebraic layer does not need primality.
-/
abbrev SquareFreePrimeState (PrimeLabel : Type*) :=
  Finset PrimeLabel

/-- Fermion number = number of occupied prime labels. -/
def fermionNumber {PrimeLabel : Type*} (S : SquareFreePrimeState PrimeLabel) : ℕ :=
  S.card

/-- Signed fermion parity on a square-free state. -/
def fermionParitySign {PrimeLabel : Type*} (S : SquareFreePrimeState PrimeLabel) : ℤ :=
  (-1 : ℤ) ^ S.card

/--
Energy of a square-free fermionic state, given one-particle energies.

For the primon gas specialization, use `energy p = log p`.
-/
def squareFreeEnergy
    {PrimeLabel : Type*}
    (energy : PrimeLabel → ℝ)
    (S : SquareFreePrimeState PrimeLabel) : ℝ :=
  ∑ p ∈ S, energy p

/--
Multiplicative Boltzmann weight of a square-free state.

For the primon gas specialization, use `x p = p^{-β}` or
`x p = exp (-β * log p)`.
-/
def squareFreeWeight
    {PrimeLabel R : Type*} [CommMonoid R]
    (x : PrimeLabel → R)
    (S : SquareFreePrimeState PrimeLabel) : R :=
  ∏ p ∈ S, x p

/-! ## 2. Finite partition functions -/

/--
Signed finite fermionic partition product:

`∏ p ∈ S, (1 - x p)`.

This is the finite square-free Möbius/supertrace product.
-/
def signedFermionPartition
    {PrimeLabel R : Type*} [CommRing R]
    (S : Finset PrimeLabel)
    (x : PrimeLabel → R) : R :=
  ∏ p ∈ S, (1 - x p)

/--
Unsigned finite fermionic square-free partition product:

`∏ p ∈ S, (1 + x p)`.

This counts square-free states without the `(-1)^F` sign.
-/
def unsignedFermionPartition
    {PrimeLabel R : Type*} [CommRing R]
    (S : Finset PrimeLabel)
    (x : PrimeLabel → R) : R :=
  ∏ p ∈ S, (1 + x p)

/--
Finite bosonic prime gas partition product:

`∏ p ∈ S, (1 - x p)⁻¹`.

For the primon gas specialization, `x p = p^{-β}`.
-/
def bosonPartition
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (x : PrimeLabel → R) : R :=
  ∏ p ∈ S, (1 - x p)⁻¹

/-! ## 3. Finite supersymmetric cancellation -/

/--
Finite boson × signed-fermion cancellation.

This is the finite theorem-root behind the formal identity

`ζ(β) * 1/ζ(β) = 1`.

The infinite zeta statement requires a separate analytic/convergence owner.
-/
theorem boson_mul_signedFermion_cancel
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (x : PrimeLabel → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    bosonPartition S x * signedFermionPartition S x = 1 := by
  unfold bosonPartition signedFermionPartition
  calc
    (∏ p ∈ S, (1 - x p)⁻¹) * (∏ p ∈ S, (1 - x p))
        = ∏ p ∈ S, ((1 - x p)⁻¹ * (1 - x p)) := by
            rw [← Finset.prod_mul_distrib]
    _ = ∏ _p ∈ S, (1 : R) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact inv_mul_cancel₀ (h p hp)
    _ = 1 := by
            simp

/--
Signed-fermion × boson cancellation.

Same theorem as `boson_mul_signedFermion_cancel`, with the factors reversed.
-/
theorem signedFermion_mul_boson_cancel
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (x : PrimeLabel → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    signedFermionPartition S x * bosonPartition S x = 1 := by
  unfold bosonPartition signedFermionPartition
  calc
    (∏ p ∈ S, (1 - x p)) * (∏ p ∈ S, (1 - x p)⁻¹)
        = ∏ p ∈ S, ((1 - x p) * (1 - x p)⁻¹) := by
            rw [← Finset.prod_mul_distrib]
    _ = ∏ _p ∈ S, (1 : R) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact mul_inv_cancel₀ (h p hp)
    _ = 1 := by
            simp

/-! ## 4. Prime DG-superalgebra sockets, no laws bundled -/

/--
Carrier for a possible differential on a prime superalgebra.

No `d² = 0` or graded Leibniz rule is bundled here.
Those must be proved by an owner module.
-/
structure PrimeDifferentialCarrier (A : Type*) where
  d : A → A

/-- External predicate: the differential squares to zero. -/
def IsNilpotentDifferential
    {A : Type*} [Zero A]
    (D : PrimeDifferentialCarrier A) : Prop :=
  ∀ a : A, D.d (D.d a) = 0

/--
External predicate: a graded Leibniz rule.

`paritySign a` should be `+1` for even and `-1` for odd.
-/
def IsGradedLeibniz
    {A : Type*} [Ring A]
    (D : PrimeDifferentialCarrier A)
    (paritySign : A → ℤ) : Prop :=
  ∀ a b : A,
    D.d (a * b) =
      D.d a * b + (Int.cast (paritySign a) : A) * a * D.d b

end InfoGeometry.Arithmetic.PrimeBosonFermionGas
