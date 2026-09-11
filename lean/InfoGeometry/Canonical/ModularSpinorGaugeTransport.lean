import InfoGeometry.Canonical.SuperKahlerModularSpinors
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QuantumKMSSymmetricSpace
import InfoGeometry.Canonical.G2HolonomyGaugeConnections

namespace InfoGeometry.Canonical

/-!
# Modular spinor gauge transport

This file adds the next honest topological node after
`SuperKahlerModularSpinors`. The current repository does not yet contain a
native supercharge or super-Kähler form, so this bridge packages only the data
that already exists natively:

* the seven-dimensional split-`G₂` carrier `QuantumKMSCarrier`;
* discrete split-`G₂` gauge transport on that carrier;
* the finite-dimensional KMS state from the matrix owner.

It therefore extends the DAG without inventing unsupported spinor dynamics.
-/

/-- The carrier currently available to the modular-spinor lane. -/
noncomputable abbrev ModularSpinorCarrier := QuantumKMSCarrier

/-- The discrete gauge connection currently available to the modular-spinor lane. -/
abbrev ModularSpinorGaugeConnection (E : Type*) := SplitG2GaugeConnection E

/-- Parallel transport in the modular-spinor lane is the native split-`G₂` transport. -/
abbrev modularSpinorTransport {E : Type*} (A : ModularSpinorGaugeConnection E) :
    List E → SplitG2Automorphism :=
  parallelTransport A

/-- The current modular-spinor carrier is seven-dimensional. -/
theorem modularSpinorCarrier_finrank :
    Module.finrank ℚ ModularSpinorCarrier = 7 :=
  quantumKMSCarrier_finrank

/-- Modular-spinor transport preserves the canonical split-`G₂` three-form. -/
theorem modularSpinorTransport_preserves_threeForm
    {E : Type*} (A : ModularSpinorGaugeConnection E) (path : List E)
    (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        (modularSpinorTransport A path x)
        (modularSpinorTransport A path y)
        (modularSpinorTransport A path z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact parallelTransport_preserves_threeForm A path x y z

/-- Triangle curvature in the modular-spinor lane is the native split-`G₂` curvature. -/
abbrev modularSpinorCurvature {E : Type*} (A : ModularSpinorGaugeConnection E)
    (e₁ e₂ e₃ : E) : SplitG2Automorphism :=
  curvature A e₁ e₂ e₃

/-- Modular-spinor curvature preserves the canonical split-`G₂` three-form. -/
theorem modularSpinorCurvature_preserves_threeForm
    {E : Type*} (A : ModularSpinorGaugeConnection E)
    (e₁ e₂ e₃ : E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        (modularSpinorCurvature A e₁ e₂ e₃ x)
        (modularSpinorCurvature A e₁ e₂ e₃ y)
        (modularSpinorCurvature A e₁ e₂ e₃ z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact curvature_preserves_threeForm A e₁ e₂ e₃ x y z

/-- The finite-dimensional KMS owner remains available on the modular-spinor lane. -/
theorem modularSpinorFiniteKMS_kms
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ ρ_inv : Matrix n n ℂ)
    (A B : Matrix n n ℂ)
    (h_inv_left : ρ_inv * ρ = 1)
    (h_inv_right : ρ * ρ_inv = 1) :
    finiteKMSState ρ (A * modularAutomorphism_i ρ ρ_inv B) =
      finiteKMSState ρ (B * A) := by
  exact finiteKMSState_kms ρ ρ_inv A B h_inv_left h_inv_right

end InfoGeometry.Canonical
