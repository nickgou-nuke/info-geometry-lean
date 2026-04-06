import InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
import InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge
import InfoGeometry.Canonical.WeylTransportChiralBridge
import InfoGeometry.Canonical.ConformalAnomalySource
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge

Causal bridge from corrected owner phase rotation into the Weyl transport
branch through the conformal projector-obstruction operator and its terminal
holonomy norm.

This file is intentionally thin:
- owner -> KKT dilation corridor
- KKT wings -> obstruction operator block decomposition
- flat Weyl transport -> obstruction norm endpoint
- `chiralScale` only as a compatibility corollary
-/

namespace InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
open InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge
open InfoGeometry.Canonical.WeylTransportBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.ChiralCartanCore
open InfoGeometry.Canonical.RelativeModularRecomposition
open InfoGeometry.Canonical.ConformalUnification.ConformalInference
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
variable [AddCommGroup A] [Module ℝ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Terminal Weyl endpoint corollary from a flat transport bridge.

Authoritative source-driven theorems are in the KKT-wing and trunk packages
below, where this norm statement is used as the last step. -/
@[rep_depth krein] theorem holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  simpa using
    WeylTransportBridge.holonomy_eq_projectorObstruction_nnnorm_of_flat
      (CI := CCI.toConformalInference)
      (Δ := Δ)
      (γ := γ)
      (bridge := bridge)
      (B := B)
      hFlat

omit [FiniteDimensional ℝ E] in
/-- Flat Weyl transport collapses to the conformal chiral scale coming from the
certified conformal inference.

This is a compatibility corollary; the primary bridge target is the
projector-obstruction norm. -/
@[rep_depth krein] theorem holonomy_eq_chiralScale_of_flat_from_conformal_compat
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = CCI.toConformalInference.chiralScale := by
  simpa using
    WeylTransportBridge.holonomy_eq_chiralScale_of_flat_compat
      (CI := CCI.toConformalInference)
      (Δ := Δ)
      (γ := γ)
      (bridge := bridge)
      (B := B)
      hFlat

/-- Leaf bundle for Weyl transport generated from conformal projector
obstruction data. -/
@[rep_depth krein] structure WeylLeafOutputs
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X) where
  lineIntegrator : WeylLineIntegrator I A A
  holonomyMap : WeylHolonomyMap A ℝ
  holonomy_eq_projectorObstruction_nnnorm :
    ∀ B : WeylGaugeField X A,
      WeylGaugeField.IsFlat (Δ := Δ) B →
      lineIntegrator.holonomy holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊

@[rep_depth krein] def WeylLeafOutputs.ofFlatBridge
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ)) :
    WeylLeafOutputs (CCI := CCI) (Δ := Δ) (γ := γ) := by
  refine
    { lineIntegrator := bridge.lineIntegrator
      holonomyMap := bridge.holonomyMap
      holonomy_eq_projectorObstruction_nnnorm := ?_ }
  intro B hFlat
  exact holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal
    (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

section

omit [FiniteDimensional ℝ E]

/-- Scalar compatibility corollary for a Weyl leaf output. -/
@[rep_depth krein] theorem WeylLeafOutputs.holonomy_eq_chiralScale_compat
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (leaf : WeylLeafOutputs (CCI := CCI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    leaf.lineIntegrator.holonomy leaf.holonomyMap B γ = CCI.toConformalInference.chiralScale := by
  calc
    leaf.lineIntegrator.holonomy leaf.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
          exact leaf.holonomy_eq_projectorObstruction_nnnorm B hFlat
    _ = CCI.toConformalInference.chiralScale :=
      CCI.toConformalInference.projectorObstruction_nnnorm_eq_chiralScale

end

end WeylLeaf

section WeylLeafThin

variable {I X A E : Type*}
variable [AddCommGroup A] [Module ℝ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Thin compatibility wrapper exposing the scalar corollary from the
operator-first bridge. -/
@[rep_depth krein] theorem holonomy_eq_chiralScale_of_flat_from_conformal_compat_thin
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = CCI.toConformalInference.chiralScale := by
  simpa using
    holonomy_eq_chiralScale_of_flat_from_conformal_compat
      (CCI := CCI)
      (Δ := Δ)
      (γ := γ)
      (bridge := bridge)
      (B := B)
      hFlat

omit [FiniteDimensional ℝ E] in
/-- Nonvanishing phase-space corollary:
if Drazin and Moore-Penrose projectors do not commute, flat Weyl holonomy is
nonzero on the conformal projector-obstruction lane. -/
@[rep_depth krein] theorem holonomy_ne_zero_of_flat_from_conformal_of_noncommute
    (CCI : CertifiedConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hNonComm :
      CCI.toConformalInference.P_D.comp CCI.toConformalInference.P_MP
        ≠ CCI.toConformalInference.P_MP.comp CCI.toConformalInference.P_D) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ ≠ 0 := by
  exact WeylTransportBridge.holonomy_ne_zero_of_flat_of_noncommute
    (CI := CCI.toConformalInference)
    (Δ := Δ)
    (γ := γ)
    (bridge := bridge)
    (B := B)
    hFlat
    hNonComm

end WeylLeafThin

section WeylLeafFromTrunk

variable {I X A E : Type*}
variable [AddCommGroup A] [Module ℝ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {α βplus βminus : Type*} [Fintype α] [Nonempty α]
variable [Fintype βplus] [Nonempty βplus]
variable [Fintype βminus] [Nonempty βminus]

omit [FiniteDimensional ℝ E] in
/-- Weyl holonomy collapses to the projector-obstruction norm directly from the
conformal inference lane; this is the norm-first anomaly-source identity. -/
@[rep_depth krein] theorem holonomy_eq_projectorObstruction_norm_of_flat_from_conformal
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      =
        ‖CCI.toConformalInference.spectralChiralProjector
            * CCI.toConformalInference.metricChiralProjector
            - CCI.toConformalInference.metricChiralProjector
                * CCI.toConformalInference.spectralChiralProjector‖₊ := by
  have _ : Nontrivial E := inferInstance
  have hHol :
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
    exact
      WeylTransportBridge.holonomy_eq_projectorObstruction_nnnorm_of_flat
        (CI := CCI.toConformalInference)
        (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat
  have hObs :=
    ConformalInference.projectorObstruction_eq_commutator
      (CI := CCI.toConformalInference)
  simpa [hObs] using hHol

omit [FiniteDimensional ℝ E] in
/-- General-case Weyl bridge through the explicit obstruction operator alias:
no vanishing assumption is used. -/
@[rep_depth krein] theorem holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal_doubled
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  have _ : Nontrivial E := inferInstance
  exact
    WeylTransportBridge.holonomy_eq_projectorObstruction_nnnorm_of_flat
      (CI := CCI.toConformalInference)
      (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

omit [Nontrivial E] in
/-- Dilation/anomaly driver from the conformal operator lane: under the
right-projector commutation hypothesis, the spectral-projector/dilation
commutator is exactly minus one half of the projector obstruction. -/
@[rep_depth krein] theorem
    spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_from_conformal
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (hRight :
      CCI.toConformalInference.P_D * CCI.toConformalInference.P_MP_right
        = CCI.toConformalInference.P_MP_right * CCI.toConformalInference.P_D) :
    CCI.toConformalInference.P_D * CCI.toConformalInference.D
        - CCI.toConformalInference.D * CCI.toConformalInference.P_D
      = -((2 : ℝ)⁻¹) • CCI.toConformalInference.projectorObstruction := by
  simpa using
    ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_rightProjector_commute
      (CI := CCI.toConformalInference) hRight

/-- Full operator-to-Weyl package under right-projector commutation:
the dilation commutator is sourced by projector obstruction, and flat Weyl
transport lands on the obstruction norm. -/
@[rep_depth krein] theorem
    rightProjector_commute_dilation_driver_and_holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (hRight :
      CCI.toConformalInference.P_D * CCI.toConformalInference.P_MP_right
        = CCI.toConformalInference.P_MP_right * CCI.toConformalInference.P_D)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    (CCI.toConformalInference.P_D * CCI.toConformalInference.D
        - CCI.toConformalInference.D * CCI.toConformalInference.P_D
      = -((2 : ℝ)⁻¹) • CCI.toConformalInference.projectorObstruction)
      ∧
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  refine ⟨?_, ?_⟩
  · exact
      spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_from_conformal
        (CCI := CCI) hRight
  · exact
      holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal_doubled
        (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

/-- Authoritative source-driven Weyl package:
right-projector commutation gives the dilation-source identity, KKT wings force
projector-obstruction block structure, and flat transport contributes only the
terminal norm endpoint. -/
@[rep_depth krein] structure SourceSpineAndWeylEndpoint
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (X0 : InfoGeometry.Quantum.RealSplitCl11Action (DoubledSpace E))
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ)) (B : WeylGaugeField X A) where
  dilation_source :
    CCI.toConformalInference.P_D * CCI.toConformalInference.D
      - CCI.toConformalInference.D * CCI.toConformalInference.P_D
    = -((2 : ℝ)⁻¹) • CCI.toConformalInference.projectorObstruction
  obstruction_isGZero :
    IsGZero X0 CCI.toConformalInference.projectorObstruction
  obstruction_diagonal_blocks :
    CCI.toConformalInference.projectorObstruction
      = plusProjector X0
          * CCI.toConformalInference.projectorObstruction
          * plusProjector X0
        + minusProjector X0
          * CCI.toConformalInference.projectorObstruction
          * minusProjector X0
  obstruction_plusProjector_mul_mul_minusProjector_eq_zero :
    plusProjector X0
        * CCI.toConformalInference.projectorObstruction
        * minusProjector X0 = 0
  obstruction_minusProjector_mul_mul_plusProjector_eq_zero :
    minusProjector X0
        * CCI.toConformalInference.projectorObstruction
        * plusProjector X0 = 0
  holonomy_eq_projectorObstruction_nnnorm :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = ‖CCI.toConformalInference.projectorObstruction‖₊

@[rep_depth krein] theorem
    kkt_wings_dilation_source_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (hRight :
      CCI.toConformalInference.P_D * CCI.toConformalInference.P_MP_right
        = CCI.toConformalInference.P_MP_right * CCI.toConformalInference.P_D)
    (hA : IsGOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A)
    (hAMP : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_MP)
    (hAD : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_D)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    SourceSpineAndWeylEndpoint
      (CCI := CCI)
      (X0 := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) := by
  let X0 : InfoGeometry.Quantum.RealSplitCl11Action (DoubledSpace E) :=
    InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)
  have hDil :
      CCI.toConformalInference.P_D * CCI.toConformalInference.D
          - CCI.toConformalInference.D * CCI.toConformalInference.P_D
        = -((2 : ℝ)⁻¹) • CCI.toConformalInference.projectorObstruction := by
    exact
      spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_from_conformal
        (CCI := CCI) hRight
  have hObsG0 :
      IsGZero X0 CCI.toConformalInference.projectorObstruction := by
    simpa [X0] using
      ConformalInference.projectorObstruction_isGZero_of_kkt_wings
        (CI := CCI.toConformalInference) (X := X0) hA hAMP hAD
  have hDiag :
      CCI.toConformalInference.projectorObstruction
        = plusProjector X0
            * CCI.toConformalInference.projectorObstruction
            * plusProjector X0
          + minusProjector X0
            * CCI.toConformalInference.projectorObstruction
            * minusProjector X0 := by
    simpa [X0] using
      ConformalInference.projectorObstruction_eq_diagonal_blocks_of_kkt_wings
        (CI := CCI.toConformalInference) (X := X0) hA hAMP hAD
  have hPlusOff :
      plusProjector X0
          * CCI.toConformalInference.projectorObstruction
          * minusProjector X0 = 0 := by
    simpa [X0] using
      ConformalInference.projectorObstruction_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings
        (CI := CCI.toConformalInference) (X := X0) hA hAMP hAD
  have hMinusOff :
      minusProjector X0
          * CCI.toConformalInference.projectorObstruction
          * plusProjector X0 = 0 := by
    simpa [X0] using
      ConformalInference.projectorObstruction_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings
        (CI := CCI.toConformalInference) (X := X0) hA hAMP hAD
  have hHol :
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
    exact holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal_doubled
      (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat
  refine
    { dilation_source := hDil
      obstruction_isGZero := hObsG0
      obstruction_diagonal_blocks := hDiag
      obstruction_plusProjector_mul_mul_minusProjector_eq_zero := hPlusOff
      obstruction_minusProjector_mul_mul_plusProjector_eq_zero := hMinusOff
      holonomy_eq_projectorObstruction_nnnorm := hHol }

/-- Operator-level KKT bridge: explicit `g₁/g₋₁` wing data force the projector
obstruction operator into grade zero on the doubled split-`Cl(1,1)` carrier. -/
@[rep_depth krein] theorem projectorObstruction_isGZero_of_kkt_wings
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (hA : IsGOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A)
    (hAMP : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_MP)
    (hAD : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_D) :
    IsGZero (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      CCI.toConformalInference.projectorObstruction := by
  have _ : Nontrivial E := inferInstance
  simpa using
    ConformalInference.projectorObstruction_isGZero_of_kkt_wings
      (CI := CCI.toConformalInference)
      (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      hA hAMP hAD

omit [FiniteDimensional ℝ E] in
/-- Weyl holonomy from an operator-level driver: if the projector-obstruction
operator is known to be grade zero, holonomy is exactly the norm of its
`g₀` lift. -/
@[rep_depth krein] theorem
    holonomy_eq_gZeroPart_projectorObstruction_nnnorm_of_flat_of_projectorObstruction_isGZero
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hObsG0 : IsGZero (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      CCI.toConformalInference.projectorObstruction) :
    let X0 : InfoGeometry.Quantum.RealSplitCl11Action (DoubledSpace E) :=
      InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = ‖InfoGeometry.Canonical.KKTCore.gZeroPart X0
          CCI.toConformalInference.projectorObstruction‖₊ := by
  have _ : Nontrivial E := inferInstance
  let X0 : InfoGeometry.Quantum.RealSplitCl11Action (DoubledSpace E) :=
    InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)
  have hEq :
      CCI.toConformalInference.projectorObstruction
        = InfoGeometry.Canonical.KKTCore.gZeroPart X0
            CCI.toConformalInference.projectorObstruction := by
    simpa [X0] using hObsG0.symm
  have hHolObs :
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
    exact
      holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal_doubled
        (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat
  have hNormEq :
      (‖CCI.toConformalInference.projectorObstruction‖₊ : ℝ)
        = (‖InfoGeometry.Canonical.KKTCore.gZeroPart X0
            CCI.toConformalInference.projectorObstruction‖₊ : ℝ) := by
    exact congrArg (fun T : (DoubledSpace E →L[ℝ] DoubledSpace E) => (‖T‖₊ : ℝ)) hEq
  calc
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := hHolObs
    _ = ‖InfoGeometry.Canonical.KKTCore.gZeroPart X0
          CCI.toConformalInference.projectorObstruction‖₊ := hNormEq

omit [FiniteDimensional ℝ E] in
/-- Weyl holonomy from an operator-level driver: if the projector-obstruction
operator is grade zero, the `g₀`-lift identity collapses to the obstruction
operator norm. -/
@[rep_depth krein] theorem
    holonomy_eq_projectorObstruction_nnnorm_of_flat_of_projectorObstruction_isGZero
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hObsG0 : IsGZero (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      CCI.toConformalInference.projectorObstruction) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
      = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  have _ : Nontrivial E := inferInstance
  let X0 : InfoGeometry.Quantum.RealSplitCl11Action (DoubledSpace E) :=
    InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)
  have hEq :
      CCI.toConformalInference.projectorObstruction
        = InfoGeometry.Canonical.KKTCore.gZeroPart X0
            CCI.toConformalInference.projectorObstruction := by
    simpa [X0] using hObsG0.symm
  have hHolG0 :
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖InfoGeometry.Canonical.KKTCore.gZeroPart X0
            CCI.toConformalInference.projectorObstruction‖₊ := by
    simpa [X0] using
      holonomy_eq_gZeroPart_projectorObstruction_nnnorm_of_flat_of_projectorObstruction_isGZero
        (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat hObsG0
  calc
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖InfoGeometry.Canonical.KKTCore.gZeroPart X0
            CCI.toConformalInference.projectorObstruction‖₊ := hHolG0
    _ = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
          exact
            (congrArg
              (fun T : (DoubledSpace E →L[ℝ] DoubledSpace E) => (‖T‖₊ : ℝ)) hEq).symm

/-- Causal package: explicit KKT wing data generate the projector-obstruction
operator statement, and Weyl holonomy is then a scalar corollary. -/
@[rep_depth krein] theorem
    kkt_wings_projectorObstruction_isGZero_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (hA : IsGOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A)
    (hAMP : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_MP)
    (hAD : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_D)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    IsGZero (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      CCI.toConformalInference.projectorObstruction
      ∧
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  have hObsG0 :
      IsGZero (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        CCI.toConformalInference.projectorObstruction := by
    exact projectorObstruction_isGZero_of_kkt_wings
      (CCI := CCI) hA hAMP hAD
  refine And.intro hObsG0 ?_
  exact holonomy_eq_projectorObstruction_nnnorm_of_flat_of_projectorObstruction_isGZero
    (CCI := CCI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat hObsG0

/-- Stronger operator-level package: explicit KKT wing data force the
off-diagonal obstruction blocks to vanish, and Weyl holonomy is the resulting
norm corollary. -/
@[rep_depth krein] theorem
    kkt_wings_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (hA : IsGOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A)
    (hAMP : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_MP)
    (hAD : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_D)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    gOnePart (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        CCI.toConformalInference.projectorObstruction = 0
      ∧
      gNegOnePart (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        CCI.toConformalInference.projectorObstruction = 0
      ∧
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  refine And.intro ?_ ?_
  · exact ConformalInference.projectorObstruction_gOnePart_eq_zero_of_kkt_wings
      (CI := CCI.toConformalInference)
      (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      hA hAMP hAD
  · refine And.intro ?_ ?_
    · exact ConformalInference.projectorObstruction_gNegOnePart_eq_zero_of_kkt_wings
        (CI := CCI.toConformalInference)
        (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        hA hAMP hAD
    · exact
        (kkt_wings_projectorObstruction_isGZero_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
          (CCI := CCI) hA hAMP hAD
          (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat).2

/-- Primary operator package for the Weyl lane: under explicit KKT wing data,
the projector obstruction is exactly its diagonal block decomposition, the
off-diagonal blocks vanish, and Weyl holonomy is only the terminal norm
corollary. -/
@[rep_depth krein] theorem
    kkt_wings_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (hA : IsGOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A)
    (hAMP : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_MP)
    (hAD : IsGNegOne (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) CCI.A_D)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    CCI.toConformalInference.projectorObstruction
      = plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        + minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      ∧
      plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
      ∧
      minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
      ∧
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  refine And.intro ?_ ?_
  · exact ConformalInference.projectorObstruction_eq_diagonal_blocks_of_kkt_wings
      (CI := CCI.toConformalInference)
      (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      hA hAMP hAD
  · refine And.intro ?_ ?_
    · exact ConformalInference.projectorObstruction_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings
        (CI := CCI.toConformalInference)
        (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        hA hAMP hAD
    · refine And.intro ?_ ?_
      · exact ConformalInference.projectorObstruction_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings
          (CI := CCI.toConformalInference)
          (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          hA hAMP hAD
      · exact
          (kkt_wings_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
            (CCI := CCI) hA hAMP hAD
            (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat).2.2

/-- Leaf-facing operator package: leaf-provided wing witnesses force the
off-diagonal obstruction blocks to vanish, and Weyl holonomy is the norm
corollary. -/
@[rep_depth krein] theorem
    leaf_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (R : PolarizedRecompositionData E α βplus βminus)
    (leaf : InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.LeafOutputs
      E α βplus βminus CCI R)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    gOnePart (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        CCI.toConformalInference.projectorObstruction = 0
      ∧
      gNegOnePart (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        CCI.toConformalInference.projectorObstruction = 0
      ∧
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  exact
    kkt_wings_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
      (CCI := CCI)
      leaf.CCI_A_isGOne
      leaf.CCI_AMP_isGNegOne
      leaf.CCI_AD_isGNegOne
      (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

/-- Leaf-facing primary operator package: the leaf-provided wing witnesses
force the full diagonal block decomposition of the obstruction operator, the
off-diagonal blocks vanish, and holonomy is only the terminal norm corollary. -/
@[rep_depth krein] theorem
    leaf_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (R : PolarizedRecompositionData E α βplus βminus)
    (leaf : InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.LeafOutputs
      E α βplus βminus CCI R)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    CCI.toConformalInference.projectorObstruction
      = plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        + minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      ∧
      plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
      ∧
      minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
      ∧
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  exact
    kkt_wings_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
      (CCI := CCI)
      leaf.CCI_A_isGOne
      leaf.CCI_AMP_isGNegOne
      leaf.CCI_AD_isGNegOne
      (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

/-- Trunk-facing operator package: trunk-provided wing witnesses force the
off-diagonal obstruction blocks to vanish, and Weyl holonomy is the norm
corollary. -/
@[rep_depth krein] theorem
    trunk_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CIK : CertifiedInverseKernel (DoubledSpace E))
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (R : PolarizedRecompositionData E α βplus βminus)
    (trunk :
      InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs
        E α βplus βminus CIK CCI R)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    gOnePart (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        CCI.toConformalInference.projectorObstruction = 0
      ∧
      gNegOnePart (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        CCI.toConformalInference.projectorObstruction = 0
      ∧
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  exact
    kkt_wings_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
      (CCI := CCI)
      trunk.CCI_A_isGOne
      trunk.CCI_AMP_isGNegOne
      trunk.CCI_AD_isGNegOne
      (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

/-- Trunk-facing primary operator package: the trunk-provided wing witnesses
force the full diagonal block decomposition of the obstruction operator, the
off-diagonal blocks vanish, and holonomy is only the terminal norm corollary. -/
@[rep_depth krein] theorem
    trunk_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CIK : CertifiedInverseKernel (DoubledSpace E))
    (CCI : CertifiedConformalInference (DoubledSpace E))
    (R : PolarizedRecompositionData E α βplus βminus)
    (trunk :
      InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs
        E α βplus βminus CIK CCI R)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge
        (CI := CCI.toConformalInference) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    CCI.toConformalInference.projectorObstruction
      = plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
        + minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      ∧
      plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
      ∧
      minusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
          * CCI.toConformalInference.projectorObstruction
          * plusProjector (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) = 0
      ∧
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ
        = ‖CCI.toConformalInference.projectorObstruction‖₊ := by
  exact
    kkt_wings_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat
      (CCI := CCI)
      trunk.CCI_A_isGOne
      trunk.CCI_AMP_isGNegOne
      trunk.CCI_AD_isGNegOne
      (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

end WeylLeafFromTrunk

end InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge
