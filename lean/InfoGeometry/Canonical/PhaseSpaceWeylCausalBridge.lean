import InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
import InfoGeometry.Canonical.WeylTransportChiralBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge

Causal bridge from corrected owner phase rotation into the Weyl transport
branch through the conformal chiral scale.

This file is intentionally thin:
- it reuses the corrected owner → KKT dilation operator corridor,
- and it reuses the flat-curvature Weyl transport → chiral scale bridge,
  specialized to the conformal inference coming from the certified conformal
  package.
-/

namespace InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge

open InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
open InfoGeometry.Canonical.WeylTransportBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Krein

section OwnerToKKT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The corrected owner phase rotation realizes as the KKT dilation operator. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ)
      = (dilationOperator (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) :=
  PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator
    (H := H) ρ

end OwnerToKKT

section WeylLeaf

variable {I X A E : Type*}
variable [Fintype I]
variable [AddCommGroup A] [Module ℝ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Flat Weyl transport collapses to the conformal chiral scale coming from the
certified conformal inference. -/
@[rep_depth krein] theorem holonomy_eq_chiralScale_of_flat_from_conformal
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureChiralScaleBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = CCI.toConformalInference.chiralScale := by
  have _ := (inferInstance : Fintype I)
  simpa using
    holonomy_eq_chiralScale_of_flat
      (CI := CCI.toConformalInference)
      (Δ := Δ)
      (γ := γ)
      (bridge := bridge)
      (B := B)
      hFlat

/-- Leaf bundle for Weyl transport generated from conformal chiral scale. -/
@[rep_depth krein] structure WeylLeafOutputs
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X) where
  lineIntegrator : WeylLineIntegrator I A A
  holonomyMap : WeylHolonomyMap A ℝ
  holonomy_eq_chiralScale :
    ∀ B : WeylGaugeField X A,
      WeylGaugeField.IsFlat (Δ := Δ) B →
      lineIntegrator.holonomy holonomyMap B γ = CCI.toConformalInference.chiralScale

@[rep_depth krein] def WeylLeafOutputs.ofFlatBridge
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureChiralScaleBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ)) :
    WeylLeafOutputs (CCI := CCI) (Δ := Δ) (γ := γ) := by
  refine
    { lineIntegrator := bridge.lineIntegrator
      holonomyMap := bridge.holonomyMap
      holonomy_eq_chiralScale := ?_ }
  intro B hFlat
  exact holonomy_eq_chiralScale_of_flat_from_conformal
    (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

end WeylLeaf

section WeylLeafThin

variable {I X A E : Type*}
variable [Fintype I]
variable [AddCommGroup A] [Module ℝ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Thin wrapper for the Weyl-to-chiral-scale bridge, avoiding unused finite
dimensional assumptions in callers. -/
@[rep_depth krein] theorem holonomy_eq_chiralScale_of_flat_from_conformal_thin
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureChiralScaleBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = CCI.toConformalInference.chiralScale := by
  simpa using
    holonomy_eq_chiralScale_of_flat_from_conformal
      (CCI := CCI)
      (Δ := Δ)
      (γ := γ)
      (bridge := bridge)
      (B := B)
      hFlat

end WeylLeafThin

end InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge
