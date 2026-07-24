import Mathlib
import InfoGeometry.Algebra.CuntzKMSState
import InfoGeometry.Algebra.CuntzGNSRepresentation
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz Representation Layer

This file records the algebraic pieces that are already available in the repo:

* the diagonal KMS inner product on coefficient vectors, via
  `CuntzGNSRepresentation.kmsInner`;
* the left-regular action of the Cuntz algebra on itself.

The analytic Hilbert-space completion and full Fock-space identification are
not asserted here.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzKMSState
open InfoGeometry.Algebra.CuntzGNSRepresentation
open scoped ComplexConjugate

noncomputable section

namespace InfoGeometry.Algebra.CuntzFockRepresentation

open InfoGeometry.Algebra.CuntzTensorQuotient

variable {n : ℕ}

/-- The diagonal weighted inner product used by the GNS construction. -/
abbrev diagonalKMSInner (n : ℕ) (primes : Fin n → ℕ) (β : ℂ)
    (a b : Fin n → ℂ) : ℂ :=
  CuntzGNSRepresentation.kmsInner n primes β a b

theorem diagonalKMSInner_hermitian (n : ℕ) (primes : Fin n → ℕ) (β : ℂ)
    (hWeightReal : ∀ i, star (kmsWeight n primes β i) = kmsWeight n primes β i)
    (a b : Fin n → ℂ) :
    star (diagonalKMSInner n primes β b a) = diagonalKMSInner n primes β a b := by
  simpa [diagonalKMSInner] using
    InfoGeometry.Algebra.CuntzGNSRepresentation.kmsInner_hermitian
      n primes β hWeightReal a b

/-- Left multiplication by `a` on the Cuntz algebra. -/
noncomputable def leftMultiplication (n : ℕ) (a : CuntzAlg n) : CuntzAlg n →ₗ[ℂ] CuntzAlg n :=
  { toFun := fun x => a * x
    map_add' := mul_add a
    map_smul' := fun c x => by
      dsimp
      simp [Algebra.smul_def, mul_assoc, Algebra.commutes] }

/-- Composition of left multiplications is left multiplication by the product. -/
theorem leftMultiplication_mul (n : ℕ) (a b : CuntzAlg n) (x : CuntzAlg n) :
    leftMultiplication n a (leftMultiplication n b x) = leftMultiplication n (a * b) x := by
  dsimp [leftMultiplication]
  rw [mul_assoc]

end InfoGeometry.Algebra.CuntzFockRepresentation
