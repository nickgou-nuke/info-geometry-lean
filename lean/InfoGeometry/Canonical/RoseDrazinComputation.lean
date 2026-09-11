import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Computing the Drazin inverse from a characteristic polynomial

Theorem-safe Lean scaffold for Nicholas J. Rose,
"A Note on Computing the Drazin Inverse", Linear Algebra Appl. 15, 95--98
(1976).

Rose observes that, if the nonzero spectral part of a matrix has characteristic
polynomial `λ^s - p₁ λ^(s-1) - ... - p_s` with `p_s ≠ 0`, then the Drazin
inverse can be represented as a polynomial in the original matrix of degree at
most `n - 1`.  This file records the matrix-level computation as explicit
polynomial and matrix equalities and proves the exact scalar polynomial
identities displayed in the examples.
-/

namespace InfoGeometry.Canonical.RoseDrazinComputation

noncomputable section

/-- A polynomial expression for the inverse power used in Rose's formula. -/
structure InversePowerPolynomialIdentity (K : Type*) [Field K] where
  s : ℕ
  ell : ℕ
  p : Polynomial K
  nonzeroCharacteristicPart : Polynomial K
  inversePowerIdentity : ∀ z : K,
    nonzeroCharacteristicPart.eval z = 0 → z ^ (ell + 1) * p.eval z = 1

/-- Matrix-level Drazin polynomial computation.  `drazin` is supplied by
an owner theorem, while `rosePolynomialReadout` records Rose's formula
`Aᴰ = A^ell p(A)`. -/
structure RoseDrazinPolynomialComputation
    (K : Type*) [Field K] {n : ℕ}
    (A drazin : Matrix (Fin n) (Fin n) K) where
  ell : ℕ
  p : Polynomial K
  characteristicPolynomial : Polynomial K
  nonzeroCharacteristicPart : Polynomial K
  degreeBound : p.natDegree + ell ≤ n - 1
  rosePolynomial : Matrix (Fin n) (Fin n) K
  rosePolynomialReadout : rosePolynomial = A ^ ell * p.eval₂ (algebraMap K (Matrix (Fin n) (Fin n) K)) A
  drazin_eq_rosePolynomial : drazin = rosePolynomial

namespace RoseDrazinPolynomialComputation

variable {K : Type*} [Field K] {n : ℕ}
variable {A drazin : Matrix (Fin n) (Fin n) K}
variable (C : RoseDrazinPolynomialComputation K A drazin)

/-- Rose's computed polynomial equals the supplied Drazin inverse. -/
theorem drazin_polynomial_readout :
    drazin = A ^ C.ell * C.p.eval₂ (algebraMap K (Matrix (Fin n) (Fin n) K)) A :=
  C.drazin_eq_rosePolynomial.trans C.rosePolynomialReadout

/-- The computed Rose polynomial is explicitly the stored polynomial formula. -/
theorem rose_polynomial_formula :
    C.rosePolynomial = A ^ C.ell * C.p.eval₂ (algebraMap K (Matrix (Fin n) (Fin n) K)) A :=
  C.rosePolynomialReadout

/-- The stored Drazin matrix is explicitly the Rose polynomial. -/
theorem drazin_eq_rose_polynomial :
    drazin = C.rosePolynomial :=
  C.drazin_eq_rosePolynomial

end RoseDrazinPolynomialComputation

/-- Souriau--Frame algorithm: the final zero `B_r`, last nonzero `p_s`,
and annihilating-polynomial/index readouts are explicit equations. -/
structure SouriauFrameDrazinIndexComputation
    (K : Type*) [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) where
  B : ℕ → Matrix (Fin n) (Fin n) K
  p : ℕ → K
  rIndex : ℕ
  sIndex : ℕ
  Br_zero : B rIndex = 0
  ps_ne_zero : p sIndex ≠ 0
  annihilatingPolynomial : Polynomial K
  annihilates_A : annihilatingPolynomial.eval₂ (algebraMap K (Matrix (Fin n) (Fin n) K)) A = 0
  drazinIndex : ℕ
  drazinIndex_eq : drazinIndex = rIndex - sIndex

namespace SouriauFrameDrazinIndexComputation

variable {K : Type*} [Field K] {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) K}
variable (C : SouriauFrameDrazinIndexComputation K A)

/-- Read out the Drazin index produced by the Souriau--Frame computation. -/
theorem index_readout : C.drazinIndex = C.rIndex - C.sIndex :=
  C.drazinIndex_eq

/-- The Souriau--Frame computation exposes the final zero index directly. -/
theorem final_zero_readout : C.B C.rIndex = 0 :=
  C.Br_zero

/-- The Souriau--Frame computation exposes the last nonzero coefficient directly. -/
theorem last_nonzero_readout : C.p C.sIndex ≠ 0 :=
  C.ps_ne_zero

/-- The Souriau--Frame computation exposes the annihilating polynomial directly. -/
theorem annihilating_polynomial_readout :
    C.annihilatingPolynomial.eval₂ (algebraMap K (Matrix (Fin n) (Fin n) K)) A = 0 :=
  C.annihilates_A

/-- The Souriau--Frame computation exposes the Drazin index equality directly. -/
theorem drazin_index_eq_readout : C.drazinIndex = C.rIndex - C.sIndex :=
  C.drazinIndex_eq

/-- Read out the supplied annihilating polynomial. -/
theorem annihilates_readout :
    C.annihilatingPolynomial.eval₂ (algebraMap K (Matrix (Fin n) (Fin n) K)) A = 0 :=
  C.annihilates_A

end SouriauFrameDrazinIndexComputation

/-- Rose Example 1: from `λ² + 5λ + 1 = 0`, the inverse-power polynomial is
`λ⁻³ = -24λ - 115`. -/
theorem example1_inverse_power_identity (x : ℚ)
    (h : x ^ 2 + 5 * x + 1 = 0) :
    x ^ 3 * (-24 * x - 115) = 1 := by
  nlinarith [sq_nonneg (x ^ 2 + 5 * x + 1), h]

/-- Rose Example 1 in coefficient-polynomial form. -/
theorem example1_polynomial_eval (x : ℚ)
    (h : x ^ 2 + 5 * x + 1 = 0) :
    x ^ 3 * (Polynomial.C (-24 : ℚ) * Polynomial.X + Polynomial.C (-115 : ℚ)).eval x = 1 := by
  simp
  nlinarith [example1_inverse_power_identity x h]

/-- Rose Example 2: `λ⁴ + λ³ + λ² + λ + 1 = 0` implies `λ⁵ = 1`. -/
theorem example2_fifth_power_identity (x : ℚ)
    (h : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0) :
    x ^ 5 = 1 := by
  have hmul : (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = 0 := by
    rw [h, mul_zero]
  nlinarith [hmul]

/-- Rose Example 2 inverse-power readout: `λ * λ⁴ = 1`. -/
theorem example2_inverse_power_identity (x : ℚ)
    (h : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0) :
    x * x ^ 4 = 1 := by
  calc
    x * x ^ 4 = x ^ 5 := by ring
    _ = 1 := example2_fifth_power_identity x h

/-- Binomial nilpotent inverse-power computation for Rose Example 3. -/
structure BinomialNilpotentInversePower
    (K : Type*) [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) where
  exponent : ℕ
  nilpotent : (A - 1) ^ exponent = 0
  truncatedBinomialInverse : Matrix (Fin n) (Fin n) K
  inversePower_eq : A ^ exponent * truncatedBinomialInverse = 1

namespace BinomialNilpotentInversePower

variable {K : Type*} [Field K] {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) K}
variable (C : BinomialNilpotentInversePower K A)

/-- The nilpotent part is the canonical shifted matrix `A - 1`. -/
def nilpotentPart : Matrix (Fin n) (Fin n) K := A - 1

/-- Read out the supplied truncated-binomial inverse-power equation. -/
theorem inverse_power_readout : A ^ C.exponent * C.truncatedBinomialInverse = 1 :=
  C.inversePower_eq

/-- The stored nilpotent part is explicitly `A - 1`. -/
theorem nilpotent_part_formula :
    nilpotentPart (A := A) = A - 1 :=
  rfl

/-- The stored nilpotence equation is explicitly exposed. -/
theorem nilpotent_readout : nilpotentPart (A := A) ^ C.exponent = 0 :=
  by simpa [nilpotentPart] using C.nilpotent

end BinomialNilpotentInversePower

end

end InfoGeometry.Canonical.RoseDrazinComputation
