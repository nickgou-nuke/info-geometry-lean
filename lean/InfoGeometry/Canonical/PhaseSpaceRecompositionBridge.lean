import InfoGeometry.Canonical.PhaseSpacePolarizedBridge
import InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge
import InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
import InfoGeometry.Canonical.KKTGeneralizedMetricBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpaceRecompositionBridge

Adjacency bridge from the corrected phase-space owner to the existing
generalized-metric recomposition transport package.

This file stays narrow:

- the owner-side transport is defined by the Hestenes rotation `J ∘ ε`,
- polarized owner lifts are transported on phase space,
- and the doubled realization identifies those transported lifts with the
  maintained recomposition transport lifts already defined on the doubled side.
- at `rep_depth projective`, one coherence theorem records that the owner-side
  phase transport descends to the maintained recomposition log-shadow surface.

No new defect language is introduced here beyond that exact identification.
-/

namespace InfoGeometry.Canonical.PhaseSpaceRecompositionBridge

open InfoGeometry.Canonical.RelativeModularRecomposition
open InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
open InfoGeometry.Canonical.KKTGeneralizedMetricBridge
open InfoGeometry.Canonical.PhaseSpacePolarizedBridge
open InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge
open InfoGeometry.Canonical.RelativeModularPolarizedBridge
open InfoGeometry.Canonical.GeneralizedMetricCore
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]

/-- Owner-side phase-space transport of a polarized `+`-sector lift. -/
@[rep_depth krein]
noncomputable def PolarizedRecompositionData.plusPhaseTransportLift
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βplus) : PhaseSpaceCarrier H :=
  phaseRotation (E := H) ρ
    (PlusRestrictedRelativeModularData.phaseLift R.polarized.plus ρ b)

/-- Owner-side phase-space transport of a polarized `-`-sector lift. -/
@[rep_depth krein]
noncomputable def PolarizedRecompositionData.minusPhaseTransportLift
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βminus) : PhaseSpaceCarrier H :=
  phaseRotation (E := H) ρ
    (MinusRestrictedRelativeModularData.phaseLift R.polarized.minus ρ b)

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.plusPhaseTransportLift_realizes_as_plusMetricTransportLift
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βplus) :
    toDoubledCopyRho (E := H) ρ
        (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)
      = PolarizedRecompositionData.plusMetricTransportLift R b := by
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PlusRestrictedRelativeModularData.phaseLift R.polarized.plus ρ b))
      (toDoubledCopyRho_comp_phaseRotation_eq_dilationOperator (H := H) ρ)
  calc
    toDoubledCopyRho (E := H) ρ
        (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)
        =
          dilationOperator (E := H)
            (toDoubledCopyRho (E := H) ρ
              (PlusRestrictedRelativeModularData.phaseLift R.polarized.plus ρ b)) := by
            rw [PolarizedRecompositionData.plusPhaseTransportLift]
            change
              ((toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ))
                  (PlusRestrictedRelativeModularData.phaseLift R.polarized.plus ρ b)
                =
                  ((dilationOperator (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ))
                    (PlusRestrictedRelativeModularData.phaseLift R.polarized.plus ρ b)
            exact htransport
    _ = dilationOperator (E := H) (R.polarized.plus.lift b) := by
          rw [PolarizedRelativeModularPair.plus_realize_phaseLift (R := R.polarized) (ρ := ρ) (b := b)]
    _ = PolarizedRecompositionData.plusMetricTransportLift R b := by
          rw [PolarizedRecompositionData.plusMetricTransportLift,
            InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_metricOperator_eq_dilationOperator
              (H := H)]

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.minusPhaseTransportLift_realizes_as_minusMetricTransportLift
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βminus) :
    toDoubledCopyRho (E := H) ρ
        (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)
      = PolarizedRecompositionData.minusMetricTransportLift R b := by
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (MinusRestrictedRelativeModularData.phaseLift R.polarized.minus ρ b))
      (toDoubledCopyRho_comp_phaseRotation_eq_dilationOperator (H := H) ρ)
  calc
    toDoubledCopyRho (E := H) ρ
        (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)
        =
          dilationOperator (E := H)
            (toDoubledCopyRho (E := H) ρ
              (MinusRestrictedRelativeModularData.phaseLift R.polarized.minus ρ b)) := by
            rw [PolarizedRecompositionData.minusPhaseTransportLift]
            change
              ((toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ))
                  (MinusRestrictedRelativeModularData.phaseLift R.polarized.minus ρ b)
                =
                  ((dilationOperator (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ))
                    (MinusRestrictedRelativeModularData.phaseLift R.polarized.minus ρ b)
            exact htransport
    _ = dilationOperator (E := H) (R.polarized.minus.lift b) := by
          rw [PolarizedRelativeModularPair.minus_realize_phaseLift (R := R.polarized) (ρ := ρ) (b := b)]
    _ = PolarizedRecompositionData.minusMetricTransportLift R b := by
          rw [PolarizedRecompositionData.minusMetricTransportLift,
            InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_metricOperator_eq_dilationOperator
              (H := H)]

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.plusPhaseTransportLift_fixed_by_phaseMinusProjector
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βplus) :
    phaseMinusProjector (E := H) (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)
      = PolarizedRecompositionData.plusPhaseTransportLift R ρ b := by
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
      (toDoubledCopyRho_comp_phaseMinusProjector_eq_generalizedMetric_minusProjector
        (H := H) ρ)
  have hforward :
      toDoubledCopyRho (E := H) ρ
          (phaseMinusProjector (E := H) (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
        =
          toDoubledCopyRho (E := H) ρ
            (PolarizedRecompositionData.plusPhaseTransportLift R ρ b) := by
    calc
      toDoubledCopyRho (E := H) ρ
          (phaseMinusProjector (E := H) (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
          =
            InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector
              (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
              (toDoubledCopyRho (E := H) ρ
                (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)) := by
              simpa [LinearMap.comp_apply] using htransport
      _ =
            InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector
              (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
              (PolarizedRecompositionData.plusMetricTransportLift R b) := by
            rw [PolarizedRecompositionData.plusPhaseTransportLift_realizes_as_plusMetricTransportLift
              (R := R) (ρ := ρ) (b := b)]
      _ = PolarizedRecompositionData.plusMetricTransportLift R b := by
            exact PolarizedRecompositionData.plusMetricTransportLift_fixed_by_minusProjector
              (R := R) (b := b)
      _ =
            toDoubledCopyRho (E := H) ρ
              (PolarizedRecompositionData.plusPhaseTransportLift R ρ b) := by
            rw [PolarizedRecompositionData.plusPhaseTransportLift_realizes_as_plusMetricTransportLift
              (R := R) (ρ := ρ) (b := b)]
  exact (doubledCopyRhoEquiv (E := H) ρ).injective hforward

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_generalizedMetric_minusProjector
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βplus) :
    InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector
        (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
          InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
        (toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
      =
        toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.plusPhaseTransportLift R ρ b) := by
  have hfix :
      phaseMinusProjector (E := H) (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)
        = PolarizedRecompositionData.plusPhaseTransportLift R ρ b := by
        simpa using
          PolarizedRecompositionData.plusPhaseTransportLift_fixed_by_phaseMinusProjector
            (R := R) (ρ := ρ) (b := b)
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
      (toDoubledCopyRho_comp_phaseMinusProjector_eq_generalizedMetric_minusProjector
        (H := H) ρ)
  have htransport' :
      toDoubledCopyRho (E := H) ρ
          (phaseMinusProjector (E := H)
            (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
        =
      InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector
          (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
            InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
          (toDoubledCopyRho (E := H) ρ
            (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)) := by
    simpa [LinearMap.comp_apply] using htransport
  have htransport'' :
      toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)
        =
      InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector
          (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
            InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
          (toDoubledCopyRho (E := H) ρ
            (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)) := by
    simpa [hfix] using htransport'
  exact htransport''.symm

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_realizedMinusProjector
    (G : InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum H)
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βplus)
    (hfix : G.minusProjector (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)
      = PolarizedRecompositionData.plusPhaseTransportLift R ρ b) :
    (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedMinusProjector
      (G := G) ρ : Module.End ℝ (DoubledSpace H))
        (toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
      =
        toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.plusPhaseTransportLift R ρ b) := by
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
      (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.toDoubledCopyRho_comp_minusProjector_eq_realized
        (G := G) ρ)
  have htransport' :
      toDoubledCopyRho (E := H) ρ
          (G.minusProjector (PolarizedRecompositionData.plusPhaseTransportLift R ρ b))
        =
      (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedMinusProjector
        (G := G) ρ : Module.End ℝ (DoubledSpace H))
        (toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.plusPhaseTransportLift R ρ b)) := by
    simpa [LinearMap.comp_apply] using htransport
  simpa [hfix] using htransport'.symm


@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.minusPhaseTransportLift_fixed_by_phasePlusProjector
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βminus) :
    phasePlusProjector (E := H) (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)
      = PolarizedRecompositionData.minusPhaseTransportLift R ρ b := by
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
      (toDoubledCopyRho_comp_phasePlusProjector_eq_generalizedMetric_plusProjector
        (H := H) ρ)
  have hforward :
      toDoubledCopyRho (E := H) ρ
          (phasePlusProjector (E := H) (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
        =
          toDoubledCopyRho (E := H) ρ
            (PolarizedRecompositionData.minusPhaseTransportLift R ρ b) := by
    calc
      toDoubledCopyRho (E := H) ρ
          (phasePlusProjector (E := H) (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
          =
            InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector
              (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
              (toDoubledCopyRho (E := H) ρ
                (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)) := by
              simpa [LinearMap.comp_apply] using htransport
      _ =
            InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector
              (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
                InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
              (PolarizedRecompositionData.minusMetricTransportLift R b) := by
            rw [PolarizedRecompositionData.minusPhaseTransportLift_realizes_as_minusMetricTransportLift
              (R := R) (ρ := ρ) (b := b)]
      _ = PolarizedRecompositionData.minusMetricTransportLift R b := by
            exact PolarizedRecompositionData.minusMetricTransportLift_fixed_by_plusProjector
              (R := R) (b := b)
      _ =
            toDoubledCopyRho (E := H) ρ
              (PolarizedRecompositionData.minusPhaseTransportLift R ρ b) := by
            rw [PolarizedRecompositionData.minusPhaseTransportLift_realizes_as_minusMetricTransportLift
              (R := R) (ρ := ρ) (b := b)]
  exact (doubledCopyRhoEquiv (E := H) ρ).injective hforward

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_generalizedMetric_plusProjector
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βminus) :
    InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector
        (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
          InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
        (toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
      =
        toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.minusPhaseTransportLift R ρ b) := by
  have hfix :
      phasePlusProjector (E := H) (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)
        = PolarizedRecompositionData.minusPhaseTransportLift R ρ b := by
        simpa using
          PolarizedRecompositionData.minusPhaseTransportLift_fixed_by_phasePlusProjector
            (R := R) (ρ := ρ) (b := b)
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
      (toDoubledCopyRho_comp_phasePlusProjector_eq_generalizedMetric_plusProjector
        (H := H) ρ)
  have htransport' :
      toDoubledCopyRho (E := H) ρ
          (phasePlusProjector (E := H)
            (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
        =
      InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector
          (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
            InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
          (toDoubledCopyRho (E := H) ρ
            (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)) := by
    simpa [LinearMap.comp_apply] using htransport
  have htransport'' :
      toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)
        =
      InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector
          (InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed :
            InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed H)
          (toDoubledCopyRho (E := H) ρ
            (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)) := by
    simpa [hfix] using htransport'
  exact htransport''.symm

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_realizedPlusProjector
    (G : InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum H)
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βminus)
    (hfix : G.plusProjector (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)
      = PolarizedRecompositionData.minusPhaseTransportLift R ρ b) :
    (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedPlusProjector
      (G := G) ρ : Module.End ℝ (DoubledSpace H))
        (toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
      =
        toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.minusPhaseTransportLift R ρ b) := by
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
      (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.toDoubledCopyRho_comp_plusProjector_eq_realized
        (G := G) ρ)
  have htransport' :
      toDoubledCopyRho (E := H) ρ
          (G.plusProjector (PolarizedRecompositionData.minusPhaseTransportLift R ρ b))
        =
      (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedPlusProjector
        (G := G) ρ : Module.End ℝ (DoubledSpace H))
        (toDoubledCopyRho (E := H) ρ
          (PolarizedRecompositionData.minusPhaseTransportLift R ρ b)) := by
    simpa [LinearMap.comp_apply] using htransport
  simpa [hfix] using htransport'.symm

@[rep_depth krein] theorem
    PolarizedRecompositionData.plusPhaseTransportLift_realizes_to_minusSheet
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βplus) :
    toDoubledCopyRho (E := H) ρ
        (PolarizedRecompositionData.plusPhaseTransportLift R ρ b) ∈ minusSheet (E := H) := by
  rw [PolarizedRecompositionData.plusPhaseTransportLift_realizes_as_plusMetricTransportLift
    (R := R) (ρ := ρ) (b := b)]
  exact PolarizedRecompositionData.plusMetricTransportLift_mem_minusSheet (R := R) (b := b)

@[rep_depth krein] theorem
    PolarizedRecompositionData.minusPhaseTransportLift_realizes_to_plusSheet
    (R : PolarizedRecompositionData H α βplus βminus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : βminus) :
    toDoubledCopyRho (E := H) ρ
        (PolarizedRecompositionData.minusPhaseTransportLift R ρ b) ∈ plusSheet (E := H) := by
  rw [PolarizedRecompositionData.minusPhaseTransportLift_realizes_as_minusMetricTransportLift
    (R := R) (ρ := ρ) (b := b)]
  exact PolarizedRecompositionData.minusMetricTransportLift_mem_plusSheet (R := R) (b := b)

section CountJunction

variable {nPlus : Nat} [Nonempty (Fin nPlus)]
variable {nMinus : Nat} [Nonempty (Fin nMinus)]

/-- Recomposition-level wrapper (`+` wing) for the owner count/phase-space
junction on count rays. -/
@[rep_depth krein, capstone] theorem
    PolarizedRecompositionData.plus_phaseSpace_projectiveCount_junction_of_countRays
    (R : PolarizedRecompositionData H α (Fin nPlus) (Fin nMinus))
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
    [MeasurableSpace (Fin nPlus)] [MeasurableSingletonClass (Fin nPlus)] [Countable (Fin nPlus)]
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nPlus)
    (hcounts : ∀ i : Fin nPlus, 0 < counts i)
    (href : ∀ i : Fin nPlus, 0 < ref i)
    (hsource : R.polarized.plus.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.polarized.plus.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    (i : Fin nPlus) :
    GeneralizedMetricSeed.plusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.polarized.plus.lift i) = R.polarized.plus.lift i
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.polarized.plus.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.polarized.plus.data.localSource) i
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          counts ref hcounts href i := by
  exact
    PlusRestrictedRelativeModularData.phaseSpace_projectiveCount_junction_of_countRays
      (R := R.polarized.plus) (ρ := ρ)
      (counts := counts) (ref := ref)
      (hcounts := hcounts) (href := href)
      (hsource := hsource) (htarget := htarget) (i := i)

/-- Recomposition-level wrapper (`-` wing) for the owner count/phase-space
junction on count rays. -/
@[rep_depth krein, capstone] theorem
    PolarizedRecompositionData.minus_phaseSpace_projectiveCount_junction_of_countRays
    (R : PolarizedRecompositionData H α (Fin nPlus) (Fin nMinus))
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
    [MeasurableSpace (Fin nMinus)] [MeasurableSingletonClass (Fin nMinus)] [Countable (Fin nMinus)]
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nMinus)
    (hcounts : ∀ i : Fin nMinus, 0 < counts i)
    (href : ∀ i : Fin nMinus, 0 < ref i)
    (hsource : R.polarized.minus.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.polarized.minus.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    (i : Fin nMinus) :
    GeneralizedMetricSeed.minusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.polarized.minus.lift i) = R.polarized.minus.lift i
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.polarized.minus.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.polarized.minus.data.localSource) i
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          counts ref hcounts href i := by
  exact
    MinusRestrictedRelativeModularData.phaseSpace_projectiveCount_junction_of_countRays
      (R := R.polarized.minus) (ρ := ρ)
      (counts := counts) (ref := ref)
      (hcounts := hcounts) (href := href)
      (hsource := hsource) (htarget := htarget) (i := i)

/-- Recomposition-level weld theorem for the shared polarized count/phase-space
junction. -/
@[rep_depth krein, capstone] theorem
    PolarizedRecompositionData.phaseSpace_projectiveCount_weld_of_countRays
    (R : PolarizedRecompositionData H α (Fin nPlus) (Fin nMinus))
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
    [MeasurableSpace (Fin nPlus)] [MeasurableSingletonClass (Fin nPlus)] [Countable (Fin nPlus)]
    [MeasurableSpace (Fin nMinus)] [MeasurableSingletonClass (Fin nMinus)] [Countable (Fin nMinus)]
    (countsPlus refPlus : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nPlus)
    (hcountsPlus : ∀ i : Fin nPlus, 0 < countsPlus i)
    (hrefPlus : ∀ i : Fin nPlus, 0 < refPlus i)
    (hplusSource : R.polarized.plus.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsPlus hcountsPlus)
    (hplusTarget : R.polarized.plus.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refPlus hrefPlus)
    (countsMinus refMinus : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nMinus)
    (hcountsMinus : ∀ i : Fin nMinus, 0 < countsMinus i)
    (hrefMinus : ∀ i : Fin nMinus, 0 < refMinus i)
    (hminusSource : R.polarized.minus.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsMinus hcountsMinus)
    (hminusTarget : R.polarized.minus.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refMinus hrefMinus)
    (iPlus : Fin nPlus) (iMinus : Fin nMinus) :
    GeneralizedMetricSeed.plusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.polarized.plus.lift iPlus) = R.polarized.plus.lift iPlus
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.polarized.plus.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.polarized.plus.data.localSource) iPlus
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          countsPlus refPlus hcountsPlus hrefPlus iPlus
      ∧
    GeneralizedMetricSeed.minusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.polarized.minus.lift iMinus) = R.polarized.minus.lift iMinus
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.polarized.minus.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.polarized.minus.data.localSource) iMinus
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          countsMinus refMinus hcountsMinus hrefMinus iMinus := by
  exact
    PolarizedRelativeModularPair.phaseSpace_projectiveCount_weld_of_countRays
      (R := R.polarized) (ρ := ρ)
      (countsPlus := countsPlus) (refPlus := refPlus)
      (hcountsPlus := hcountsPlus) (hrefPlus := hrefPlus)
      (hplusSource := hplusSource) (hplusTarget := hplusTarget)
      (countsMinus := countsMinus) (refMinus := refMinus)
      (hcountsMinus := hcountsMinus) (hrefMinus := hrefMinus)
      (hminusSource := hminusSource) (hminusTarget := hminusTarget)
      (iPlus := iPlus) (iMinus := iMinus)

/--
Capstone weld package: count/projective Hamiltonian identities and phase-space
fixed-point statements on both polarized wings, together with the recomposition
log-shadow identification.
-/
@[rep_depth projective, capstone] theorem
    PolarizedRecompositionData.phaseSpace_projectiveCount_weld_identifies_twistShadow_of_countRays
    (R : PolarizedRecompositionData H α (Fin nPlus) (Fin nMinus))
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
    [MeasurableSpace (Fin nPlus)] [MeasurableSingletonClass (Fin nPlus)] [Countable (Fin nPlus)]
    [MeasurableSpace (Fin nMinus)] [MeasurableSingletonClass (Fin nMinus)] [Countable (Fin nMinus)]
    (countsPlus refPlus : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nPlus)
    (hcountsPlus : ∀ i : Fin nPlus, 0 < countsPlus i)
    (hrefPlus : ∀ i : Fin nPlus, 0 < refPlus i)
    (hplusSource : R.polarized.plus.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsPlus hcountsPlus)
    (hplusTarget : R.polarized.plus.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refPlus hrefPlus)
    (countsMinus refMinus : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nMinus)
    (hcountsMinus : ∀ i : Fin nMinus, 0 < countsMinus i)
    (hrefMinus : ∀ i : Fin nMinus, 0 < refMinus i)
    (hminusSource : R.polarized.minus.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsMinus hcountsMinus)
    (hminusTarget : R.polarized.minus.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refMinus hrefMinus)
    (iPlus : Fin nPlus) (iMinus : Fin nMinus) :
    GeneralizedMetricSeed.plusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.polarized.plus.lift iPlus) = R.polarized.plus.lift iPlus
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.polarized.plus.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.polarized.plus.data.localSource) iPlus
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          countsPlus refPlus hcountsPlus hrefPlus iPlus
      ∧
    GeneralizedMetricSeed.minusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.polarized.minus.lift iMinus) = R.polarized.minus.lift iMinus
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.polarized.minus.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.polarized.minus.data.localSource) iMinus
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          countsMinus refMinus hcountsMinus hrefMinus iMinus
      ∧
    R.couplingLogDefect = PolarizedRecompositionData.generalizedMetricTwistShadow R := by
  have hweld :
      GeneralizedMetricSeed.plusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
          (R.polarized.plus.lift iPlus) = R.polarized.plus.lift iPlus
        ∧
      InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
          (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
            (α := Fin nPlus) R.polarized.plus.data.localTarget)
          (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
            (α := Fin nPlus) R.polarized.plus.data.localSource) iPlus
        = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
            countsPlus refPlus hcountsPlus hrefPlus iPlus
        ∧
      GeneralizedMetricSeed.minusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
          (R.polarized.minus.lift iMinus) = R.polarized.minus.lift iMinus
        ∧
      InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
          (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
            (α := Fin nMinus) R.polarized.minus.data.localTarget)
          (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
            (α := Fin nMinus) R.polarized.minus.data.localSource) iMinus
        = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
            countsMinus refMinus hcountsMinus hrefMinus iMinus :=
    PolarizedRecompositionData.phaseSpace_projectiveCount_weld_of_countRays
      (R := R) (ρ := ρ)
      (countsPlus := countsPlus) (refPlus := refPlus)
      (hcountsPlus := hcountsPlus) (hrefPlus := hrefPlus)
      (hplusSource := hplusSource) (hplusTarget := hplusTarget)
      (countsMinus := countsMinus) (refMinus := refMinus)
      (hcountsMinus := hcountsMinus) (hrefMinus := hrefMinus)
      (hminusSource := hminusSource) (hminusTarget := hminusTarget)
      (iPlus := iPlus) (iMinus := iMinus)
  refine ⟨hweld.1, hweld.2.1, hweld.2.2.1, hweld.2.2.2, ?_⟩
  rfl

end CountJunction

/-- Coherence theorem: the owner-side phase transport descends to the maintained
logarithmic recomposition shadow. -/
@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.phaseTransport_descends_to_generalizedMetricTwistShadow
    (R : PolarizedRecompositionData H α βplus βminus) :
    R.couplingLogDefect = PolarizedRecompositionData.generalizedMetricTwistShadow R := rfl

end Core

end InfoGeometry.Canonical.PhaseSpaceRecompositionBridge
