import Mathlib.Tactic
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
open InfoGeometry.Algebra.CuntzGNSRepresentation
noncomputable section

namespace InfoGeometry.Algebra.CuntzFockRepresentation

open InfoGeometry.Algebra.CuntzTensorQuotient

variable {n : ℕ}

theorem nativeKMSInner_hermitian
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (hφ : ∀ a b : CuntzAlg n,
      star (φ (star a * b)) = φ (star b * a))
    (a b : CuntzAlg n) :
    star (CuntzGNSRepresentation.kmsInner φ b a) =
      CuntzGNSRepresentation.kmsInner φ a b :=
  CuntzGNSRepresentation.kmsInner_hermitian φ hφ a b

abbrev leftMultiplication := CuntzGNSRepresentation.leftMultiplication

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
