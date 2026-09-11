import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.GeneralizedMetricCore
import InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KKTGeneralizedMetricBridge

Adjacency bridge from the split-operator KKT grading to the doubled-carrier
generalized-metric seed.

This file keeps the new KKT corridor tied to the existing doubled-space root:
the canonical KKT projectors coincide with the generalized-metric projectors,
and the doubled metric operator swaps the KKT `±1` wings.
-/

namespace InfoGeometry.Canonical.KKTGeneralizedMetricBridge

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.GeneralizedMetricCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Quantum
open InfoGeometry.Krein

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H2" => DoubledSpace H
local notation "EndH" => H2 →L[ℝ] H2

@[rep_depth krein, simp] theorem canonical_plusProjector_eq_generalizedMetric_plusProjector :
    plusProjector (doubledSpaceCl11Action (E := H))
      = GeneralizedMetricSeed.plusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) := by
  rw [tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [plusProjector, doubledSpaceCl11Action, spectralPlusProj, spectral_epsilon]

@[rep_depth krein, simp] theorem canonical_minusProjector_eq_generalizedMetric_minusProjector :
    minusProjector (doubledSpaceCl11Action (E := H))
      = GeneralizedMetricSeed.minusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) := by
  rw [tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [minusProjector, doubledSpaceCl11Action, spectralMinusProj, spectral_epsilon]

@[rep_depth krein] theorem canonical_metric_comp_plusProjector :
    dilationOperator (E := H).comp (plusProjector (doubledSpaceCl11Action (E := H)))
      = (minusProjector (doubledSpaceCl11Action (E := H))).comp (dilationOperator (E := H)) := by
  rw [← tomitaGeneralizedMetricSeed_metricOperator_eq_dilationOperator (H := H)]
  rw [canonical_plusProjector_eq_generalizedMetric_plusProjector,
    canonical_minusProjector_eq_generalizedMetric_minusProjector]
  exact GeneralizedMetricSeed.metric_comp_plusProjector
    (G := (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H))

@[rep_depth krein] theorem canonical_metric_comp_minusProjector :
    dilationOperator (E := H).comp (minusProjector (doubledSpaceCl11Action (E := H)))
      = (plusProjector (doubledSpaceCl11Action (E := H))).comp (dilationOperator (E := H)) := by
  rw [← tomitaGeneralizedMetricSeed_metricOperator_eq_dilationOperator (H := H)]
  rw [canonical_plusProjector_eq_generalizedMetric_plusProjector,
    canonical_minusProjector_eq_generalizedMetric_minusProjector]
  exact GeneralizedMetricSeed.metric_comp_minusProjector
    (G := (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H))

@[rep_depth krein] theorem canonical_gZeroPart_eq_generalizedMetric_blockDiagonal
    (A : EndH) :
    gZeroPart (doubledSpaceCl11Action (E := H)) A
      =
        plusProjector (doubledSpaceCl11Action (E := H)) * A
          * plusProjector (doubledSpaceCl11Action (E := H))
        + minusProjector (doubledSpaceCl11Action (E := H)) * A
          * minusProjector (doubledSpaceCl11Action (E := H)) := by
  rfl

@[rep_depth krein] theorem toDoubledCopyRho_comp_phasePlusProjector_eq_canonical_plusProjector
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phasePlusProjector (E := H))
      = (plusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) := by
  calc
    (toDoubledCopyRho (E := H) ρ).comp (phasePlusProjector (E := H))
        = (spectralPlusProj (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) := by
            simpa using
              (InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.toDoubledCopyRho_comp_phasePlusProjector
                (E := H) ρ)
    _ = (plusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) := by
        rw [canonical_plusProjector_eq_generalizedMetric_plusProjector,
          tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj]

@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseMinusProjector_eq_canonical_minusProjector
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phaseMinusProjector (E := H))
      = (minusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) := by
  calc
    (toDoubledCopyRho (E := H) ρ).comp (phaseMinusProjector (E := H))
        = (spectralMinusProj (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) := by
            simpa using
              (InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.toDoubledCopyRho_comp_phaseMinusProjector
                (E := H) ρ)
    _ = (minusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) := by
        rw [canonical_minusProjector_eq_generalizedMetric_minusProjector,
          tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj]

@[rep_depth krein] theorem toDoubledCopyRho_comp_phasePlusProjector_eq_generalizedMetric_plusProjector
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phasePlusProjector (E := H))
      = (GeneralizedMetricSeed.plusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) := by
  calc
    (toDoubledCopyRho (E := H) ρ).comp (phasePlusProjector (E := H))
        = (plusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
            (toDoubledCopyRho (E := H) ρ) := by
            exact toDoubledCopyRho_comp_phasePlusProjector_eq_canonical_plusProjector ρ
    _ = (GeneralizedMetricSeed.plusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) := by
        rw [canonical_plusProjector_eq_generalizedMetric_plusProjector]

@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseMinusProjector_eq_generalizedMetric_minusProjector
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phaseMinusProjector (E := H))
      = (GeneralizedMetricSeed.minusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) := by
  calc
    (toDoubledCopyRho (E := H) ρ).comp (phaseMinusProjector (E := H))
        = (minusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
            (toDoubledCopyRho (E := H) ρ) := by
            exact toDoubledCopyRho_comp_phaseMinusProjector_eq_canonical_minusProjector ρ
    _ = (GeneralizedMetricSeed.minusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) := by
        rw [canonical_minusProjector_eq_generalizedMetric_minusProjector]

@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseRotation_eq_dilationOperator
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ)
      = (dilationOperator (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) := by
  calc
    (toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ)
        = (modularRotation (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) := by
            simpa using
              (InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.toDoubledCopyRho_comp_phaseRotation
                (E := H) ρ)
    _ = (dilationOperator (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) := by
        rw [show modularRotation (E := H) = InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := H) by
              rfl]
        rw [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_dilationOperator]

end Core

end InfoGeometry.Canonical.KKTGeneralizedMetricBridge
