import InfoGeometry.Algebra.CuntzLeftRightCommutant
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Left/right modular distinguishability on the native Cuntz quotient

This file records the algebraic pairing supplied by a native GNS functional.
It deliberately does not assert positivity: positivity belongs to the
corresponding positive-functional/C*-completion owner.
-/

namespace InfoGeometry.Algebra.CuntzModularDistinguishability

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzGNSRepresentation
open InfoGeometry.Algebra.CuntzLeftRightCommutant

noncomputable section

variable {n : ℕ}

abbrev CuntzOperator (n : ℕ) := CuntzAlg n →ₗ[ℂ] CuntzAlg n

/-- Difference between a left action and a right action. -/
noncomputable def leftRightActionDifference
    (n : ℕ) (a b : CuntzAlg n) : CuntzOperator n :=
  leftMultiplication n a - rightMultiplication n b

@[simp] theorem leftRightActionDifference_apply
    (n : ℕ) (a b x : CuntzAlg n) :
    leftRightActionDifference n a b x = a * x - x * b := by
  rfl

/-- The GNS sesquilinear form on `CuntzAlg n` associated to a functional `φ`. -/
noncomputable def gnsInner
    (φ : CuntzAlg n →ₗ[ℂ] ℂ) (u v : CuntzAlg n) : ℂ :=
  φ (star u * v)

@[simp] theorem gnsInner_apply
    (φ : CuntzAlg n →ₗ[ℂ] ℂ) (u v : CuntzAlg n) :
    gnsInner φ u v = φ (star u * v) :=
  rfl

theorem gnsInner_hermitian
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (hφ : ∀ u v : CuntzAlg n, star (φ (star u * v)) = φ (star v * u))
    (u v : CuntzAlg n) :
    star (gnsInner φ v u) = gnsInner φ u v :=
  hφ v u

/-- The GNS pairing of two left/right action defects.

The name records distinguishability, while the type remains the native
sesquilinear form `gnsInner`; no positivity is built in here. -/
noncomputable def modularDistinguishabilityPairing
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (a b : CuntzAlg n) (x y : CuntzAlg n) : ℂ :=
  gnsInner φ
    (leftRightActionDifference n a b x)
    (leftRightActionDifference n a b y)

@[simp] theorem modularDistinguishabilityPairing_apply
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (a b x y : CuntzAlg n) :
    modularDistinguishabilityPairing φ a b x y =
      gnsInner φ (a * x - x * b) (a * y - y * b) := by
  rfl

theorem modularDistinguishabilityPairing_hermitian
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (hφ : ∀ u v : CuntzAlg n,
      star (φ (star u * v)) = φ (star v * u))
    (a b x y : CuntzAlg n) :
    star (modularDistinguishabilityPairing φ a b y x) =
      modularDistinguishabilityPairing φ a b x y := by
  exact gnsInner_hermitian φ hφ
    (leftRightActionDifference n a b x)
    (leftRightActionDifference n a b y)

theorem modularDistinguishabilityPairing_zero_of_action_agreement
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (a b : CuntzAlg n)
    (h : ∀ x : CuntzAlg n, a * x = x * b)
    (x y : CuntzAlg n) :
    modularDistinguishabilityPairing φ a b x y = 0 := by
  dsimp [modularDistinguishabilityPairing, leftRightActionDifference, gnsInner]
  have hx : a * x - x * b = 0 := by rw [h x, sub_self]
  simp [hx]

theorem leftRightActionDifference_commutant_shadow
    (a b x : CuntzAlg n) :
    leftMultiplication n a (rightMultiplication n b x) =
      rightMultiplication n b (leftMultiplication n a x) := by
  exact left_right_commute n a b x

end

end InfoGeometry.Algebra.CuntzModularDistinguishability
