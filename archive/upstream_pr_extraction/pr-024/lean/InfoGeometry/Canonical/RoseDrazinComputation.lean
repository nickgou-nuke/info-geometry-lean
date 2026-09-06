import Mathlib

/-!
# Computing the Drazin inverse from a characteristic polynomial

Theorem-safe Lean scaffold for Nicholas J. Rose,
"A Note on Computing the Drazin Inverse", Linear Algebra Appl. 15, 95--98
(1976).

Rose observes that, if the nonzero spectral part of a matrix has characteristic
polynomial `λ^s - p₁ λ^(s-1) - ... - p_s` with `p_s ≠ 0`, then the Drazin
inverse can be represented as a polynomial in the original matrix of degree at
most `n - 1`.  This file records the matrix-level computation as explicit
certificates and proves the exact scalar polynomial identities displayed in the
examples.
-/

namespace InfoGeometry.Canonical.RoseDrazinComputation

noncomputable section

/-- A polynomial expression for the inverse power used in Rose's formula. -/
structure InversePowerPolynomialCertificate (K : Type*) [Field K] where
  s : ℕ
  ell : ℕ
  p : Polynomial K
  nonzeroCharacteristicPart : Polynomial K
  inversePowerIdentity : ∀ z : K,
    nonzeroCharacteristicPart.eval z = 0 → z ^ (ell + 1) * p.eval z = 1

/-- Matrix-level Drazin polynomial computation socket.  `drazin` is supplied by
an owner theorem, while `rosePolynomialReadout` records Rose's formula
`Aᴰ = A^ell p(A)`. -/
structure RoseDrazinPolynomialCertificate
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

namespace RoseDrazinPolynomialCertificate

variable {K : Type*} [Field K] {n : ℕ}
variable {A drazin : Matrix (Fin n) (Fin n) K}
variable (C : RoseDrazinPolynomialCertificate K A drazin)

/-- Rose's computed polynomial equals the supplied Drazin inverse. -/
theorem drazin_polynomial_readout :
    drazin = A ^ C.ell * C.p.eval₂ (algebraMap K (Matrix (Fin n) (Fin n) K)) A :=
  C.drazin_eq_rosePolynomial.trans C.rosePolynomialReadout

end RoseDrazinPolynomialCertificate

/-- Souriau--Frame algorithm socket: the final zero `B_r`, last nonzero `p_s`,
and annihilating-polynomial/index readouts are explicit certificates. -/
structure SouriauFrameDrazinIndexCertificate
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

namespace SouriauFrameDrazinIndexCertificate

variable {K : Type*} [Field K] {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) K}
variable (C : SouriauFrameDrazinIndexCertificate K A)

/-- Read out the Drazin index produced by the Souriau--Frame certificate. -/
theorem index_readout : C.drazinIndex = C.rIndex - C.sIndex :=
  C.drazinIndex_eq

/-- Read out the supplied annihilating polynomial. -/
theorem annihilates_readout :
    C.annihilatingPolynomial.eval₂ (algebraMap K (Matrix (Fin n) (Fin n) K)) A = 0 :=
  C.annihilates_A

end SouriauFrameDrazinIndexCertificate

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

/-- Binomial nilpotent socket for Rose Example 3. -/
structure BinomialNilpotentInverseCertificate
    (K : Type*) [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) where
  nilpotentPart : Matrix (Fin n) (Fin n) K := A - 1
  exponent : ℕ
  nilpotent : nilpotentPart ^ exponent = 0
  truncatedBinomialInverse : Matrix (Fin n) (Fin n) K
  inversePowerReadout : Prop
  inversePowerCertified : inversePowerReadout

namespace BinomialNilpotentInverseCertificate

variable {K : Type*} [Field K] {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) K}
variable (C : BinomialNilpotentInverseCertificate K A)

/-- Read out the supplied truncated-binomial inverse-power certificate. -/
theorem inverse_power_readout : C.inversePowerReadout :=
  C.inversePowerCertified

end BinomialNilpotentInverseCertificate

end

end InfoGeometry.Canonical.RoseDrazinComputation
