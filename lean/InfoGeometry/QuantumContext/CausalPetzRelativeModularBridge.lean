import InfoGeometry.Physics.FiniteRelativeModularOperator

/-!
# Causal compression and a finite relative modular operator

This bridge uses the repository's regular-bimodule relative modular operator
`X ↦ ρ * X * σInv`. If a causal idempotent commutes with both factors, its
corner compression commutes with that operator. This is a finite algebraic
intertwining theorem; it does not assert Petz sufficiency, relative-entropy
monotonicity, or a general quantum Markov theorem.
-/

namespace InfoGeometry.QuantumContext.CausalPetzRelativeModularBridge

open InfoGeometry.Physics.FiniteRelativeModularOperator
open InfoGeometry.Physics.RegularBimoduleCommutant

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Compression to the corner selected by `P`. -/
def causalCompression (P : A) : A →ₗ[R] A :=
  (leftAction (R := R) P).comp (rightAction (R := R) P)

@[simp] theorem causalCompression_apply (P X : A) :
    causalCompression (R := R) P X = P * X * P := by
  simp [causalCompression, leftAction, rightAction, LinearMap.comp_apply,
    mul_assoc]

/-- Corner compression intertwines with the relative modular action if the
projector commutes with its left and right factors. -/
theorem relativeModularOperator_commutes_with_causalCompression
    (rho sigmaInv P : A)
    (hρ : P * rho = rho * P)
    (hσ : P * sigmaInv = sigmaInv * P) :
    (relativeModularOperator (R := R) rho sigmaInv).comp
        (causalCompression (R := R) P) =
      (causalCompression (R := R) P).comp
        (relativeModularOperator (R := R) rho sigmaInv) := by
  ext X
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    causalCompression_apply, relativeModularOperator_apply,
    causalCompression_apply, relativeModularOperator_apply]
  calc
    rho * (P * X * P) * sigmaInv =
        (rho * P) * X * (P * sigmaInv) := by
          simp only [mul_assoc]
    _ = (P * rho) * X * (sigmaInv * P) := by rw [hρ.symm, hσ]
    _ = P * (rho * X * sigmaInv) * P := by
          simp only [mul_assoc]

/-- Pointwise form of the commutation theorem, useful for observables. -/
theorem relativeModularOperator_causalCompression_apply
    (rho sigmaInv P X : A)
    (hρ : P * rho = rho * P)
    (hσ : P * sigmaInv = sigmaInv * P) :
    relativeModularOperator (R := R) rho sigmaInv (P * X * P) =
      P * (rho * X * sigmaInv) * P := by
  have hcomm :=
    relativeModularOperator_commutes_with_causalCompression
      (R := R) rho sigmaInv P hρ hσ
  have h := congrArg (fun f : A →ₗ[R] A => f X) hcomm
  simpa [causalCompression_apply, relativeModularOperator_apply] using h

end InfoGeometry.QuantumContext.CausalPetzRelativeModularBridge
