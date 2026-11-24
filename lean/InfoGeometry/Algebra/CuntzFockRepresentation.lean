import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
noncomputable section

namespace InfoGeometry.Algebra.CuntzFockRepresentation

open InfoGeometry.Algebra.CuntzTensorQuotient

variable {n : ℕ}

theorem diagonalKMSInner_hermitian (n : ℕ) (primes : Fin n → ℕ) (β : ℂ)
    (hWeightReal : ∀ i, star (kmsWeight n primes β i) = kmsWeight n primes β i)
    (a b : Fin n → ℂ) :
    star (CuntzGNSRepresentation.kmsInner n primes β b a) =
        CuntzGNSRepresentation.kmsInner n primes β a b := by
  simpa using CuntzGNSRepresentation.kmsInner_hermitian
    n primes β hWeightReal a b

/-- Left multiplication by `a` on the Cuntz algebra. -/
noncomputable def leftMultiplication (n : ℕ) (a : CuntzAlg n) : CuntzAlg n →ₗ[ℂ] CuntzAlg n :=
  LinearMap.mulLeft ℂ a

/-- Composition of left multiplications is left multiplication by the product. -/
theorem leftMultiplication_mul (n : ℕ) (a b : CuntzAlg n) (x : CuntzAlg n) :
    leftMultiplication n a (leftMultiplication n b x) = leftMultiplication n (a * b) x := by
  simp [leftMultiplication, LinearMap.mulLeft_apply]

/-! ### Cuntz q-CCR boundary in the left-regular Fock action -/

theorem leftMultiplication_cuntz_isometry (n : ℕ) (i : Fin n) (x : CuntzAlg n) :
    leftMultiplication n (cuntzSdag n i)
        (leftMultiplication n (cuntzS n i) x) = x := by
  rw [leftMultiplication_mul, cuntz_isometry]
  simp [leftMultiplication]

theorem leftMultiplication_cuntz_qccr_zero (n : ℕ) (i : Fin n) (x : CuntzAlg n) :
    leftMultiplication n (cuntzSdag n i)
        (leftMultiplication n (cuntzS n i) x) - x = 0 := by
  rw [leftMultiplication_cuntz_isometry]
  exact sub_self x

end InfoGeometry.Algebra.CuntzFockRepresentation
