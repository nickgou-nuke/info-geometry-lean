import InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge
import InfoGeometry.Canonical.RelativeModularRecomposition
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge

Adjacency bridge from the doubled generalized-metric seed down to the current
projective recomposition defects.

This file stays disciplined:

- at `rep_depth krein` it records how the canonical generalized-metric operator
  transports polarized lifts across the plus/minus sheets,
- at `rep_depth projective` it records that the existing recomposition coupling
  defect is the projective shadow of that generalized-metric twist data.

It does **not** claim that a physical `B`-field has already been formalized.
-/

namespace InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge

open InfoGeometry.Canonical.GeneralizedMetricCore
open InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge
open InfoGeometry.Canonical.RelativeModularRecomposition
open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]

local notation "H2" => DoubledSpace H

/-- The canonical generalized-metric property induced by the polarized pair
underlying a recomposition package. -/
@[rep_depth krein]
noncomputable def PolarizedRecompositionData.toGeneralizedMetricData
    (R : PolarizedRecompositionData H α βplus βminus) :
    GeneralizedMetricPolarizedData H α βplus βminus :=
  PolarizedRelativeModularPair.toGeneralizedMetricData (R := R.polarized)

/-- Metric transport of a plus-sector lift lands on the minus side. -/
@[rep_depth krein]
noncomputable def PolarizedRecompositionData.plusMetricTransportLift
    (R : PolarizedRecompositionData H α βplus βminus) (b : βplus) : H2 :=
  (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator (R.polarized.plus.lift b)

/-- Metric transport of a minus-sector lift lands on the plus side. -/
@[rep_depth krein]
noncomputable def PolarizedRecompositionData.minusMetricTransportLift
    (R : PolarizedRecompositionData H α βplus βminus) (b : βminus) : H2 :=
  (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator (R.polarized.minus.lift b)

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.plusMetricTransportLift_fixed_by_minusProjector
    (R : PolarizedRecompositionData H α βplus βminus) (b : βplus) :
    GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
      (PolarizedRecompositionData.plusMetricTransportLift R b)
        = PolarizedRecompositionData.plusMetricTransportLift R b := by
  let u := R.polarized.plus.lift b
  have hswap :=
    congrArg (fun F : H2 →L[ℝ] H2 => F u)
      (GeneralizedMetricSeed.metric_comp_plusProjector
        (G := (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)))
  have hfix :=
    (PolarizedRecompositionData.toGeneralizedMetricData R).plus_fixed b
  have hfix' :
      GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u = u := by
    simpa [u, PolarizedRecompositionData.toGeneralizedMetricData] using hfix
  calc
    GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (PolarizedRecompositionData.plusMetricTransportLift R b)
        = (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator
            ((tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).plusProjector u) := by
            simpa [PolarizedRecompositionData.plusMetricTransportLift, u] using hswap.symm
    _ = (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator u := by
          rw [hfix']
    _ = PolarizedRecompositionData.plusMetricTransportLift R b := by
          rfl

@[rep_depth krein, simp] theorem
    PolarizedRecompositionData.minusMetricTransportLift_fixed_by_plusProjector
    (R : PolarizedRecompositionData H α βplus βminus) (b : βminus) :
    GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
      (PolarizedRecompositionData.minusMetricTransportLift R b)
        = PolarizedRecompositionData.minusMetricTransportLift R b := by
  let u := R.polarized.minus.lift b
  have hswap :=
    congrArg (fun F : H2 →L[ℝ] H2 => F u)
      (GeneralizedMetricSeed.metric_comp_minusProjector
        (G := (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)))
  have hfix :=
    (PolarizedRecompositionData.toGeneralizedMetricData R).minus_fixed b
  have hfix' :
      GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u = u := by
    simpa [u, PolarizedRecompositionData.toGeneralizedMetricData] using hfix
  calc
    GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (PolarizedRecompositionData.minusMetricTransportLift R b)
        = (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator
            ((tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).minusProjector u) := by
            simpa [PolarizedRecompositionData.minusMetricTransportLift, u] using hswap.symm
    _ = (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator u := by
          rw [hfix']
    _ = PolarizedRecompositionData.minusMetricTransportLift R b := by
          rfl

@[rep_depth krein] theorem
    PolarizedRecompositionData.plusMetricTransportLift_mem_minusSheet
    (R : PolarizedRecompositionData H α βplus βminus) (b : βplus) :
    PolarizedRecompositionData.plusMetricTransportLift R b ∈ minusSheet (E := H) := by
  rw [← PolarizedRecompositionData.plusMetricTransportLift_fixed_by_minusProjector (R := R) (b := b)]
  rw [tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj]
  exact spectralMinusProj_mem_minusSheet (E := H)
    (PolarizedRecompositionData.plusMetricTransportLift R b)

@[rep_depth krein] theorem
    PolarizedRecompositionData.minusMetricTransportLift_mem_plusSheet
    (R : PolarizedRecompositionData H α βplus βminus) (b : βminus) :
    PolarizedRecompositionData.minusMetricTransportLift R b ∈ plusSheet (E := H) := by
  rw [← PolarizedRecompositionData.minusMetricTransportLift_fixed_by_plusProjector (R := R) (b := b)]
  rw [tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj]
  exact spectralPlusProj_mem_plusSheet (E := H)
    (PolarizedRecompositionData.minusMetricTransportLift R b)

/-- Projective shadow of the generalized-metric twist in logarithmic form. -/
@[rep_depth projective]
def PolarizedRecompositionData.generalizedMetricTwistShadow
    (R : PolarizedRecompositionData H α βplus βminus) : ℝ :=
  R.couplingLogDefect

/-- Projective shadow of the generalized-metric twist in modular-potential form. -/
@[rep_depth projective]
def PolarizedRecompositionData.generalizedMetricPotentialShadow
    (R : PolarizedRecompositionData H α βplus βminus) : ℝ :=
  R.couplingPotentialDefect

@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.generalizedMetricTwistShadow_eq_couplingLogDefect
    (R : PolarizedRecompositionData H α βplus βminus) :
    PolarizedRecompositionData.generalizedMetricTwistShadow R = R.couplingLogDefect := rfl

@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.generalizedMetricPotentialShadow_eq_couplingPotentialDefect
    (R : PolarizedRecompositionData H α βplus βminus) :
    PolarizedRecompositionData.generalizedMetricPotentialShadow R = R.couplingPotentialDefect := rfl

@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_generalizedMetricTwistShadow
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedLogDensity bplus bminus
      = R.recomposedCommonCarrierLogDensity bplus bminus
          + PolarizedRecompositionData.generalizedMetricTwistShadow R := by
  rw [PolarizedRecompositionData.generalizedMetricTwistShadow]
  exact PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_coupling
    (R := R) (bplus := bplus) (bminus := bminus)

@[rep_depth projective, simp] theorem
    PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_generalizedMetricPotentialShadow
    (R : PolarizedRecompositionData H α βplus βminus) (bplus : βplus) (bminus : βminus) :
    R.recomposedModularPotential bplus bminus
      = R.recomposedCommonCarrierModularPotential bplus bminus
          + PolarizedRecompositionData.generalizedMetricPotentialShadow R := by
  rw [PolarizedRecompositionData.generalizedMetricPotentialShadow]
  exact PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_coupling
    (R := R) (bplus := bplus) (bminus := bminus)

@[rep_depth projective] theorem
    PolarizedRecompositionData.generalizedMetricTwistShadow_eq_zero_iff_exactLogRecomposition
    (R : PolarizedRecompositionData H α βplus βminus) :
    PolarizedRecompositionData.generalizedMetricTwistShadow R = 0 ↔ R.exactLogRecomposition := by
  simpa [PolarizedRecompositionData.generalizedMetricTwistShadow,
    PolarizedRecompositionData.vanishingCoupling] using
    PolarizedRecompositionData.vanishingCoupling_iff_exactLogRecomposition (R := R)

@[rep_depth projective] theorem
    PolarizedRecompositionData.generalizedMetricPotentialShadow_eq_zero_iff_exactPotentialRecomposition
    (R : PolarizedRecompositionData H α βplus βminus) :
    PolarizedRecompositionData.generalizedMetricPotentialShadow R = 0 ↔ R.exactPotentialRecomposition := by
  simpa [PolarizedRecompositionData.generalizedMetricPotentialShadow,
    PolarizedRecompositionData.vanishingCoupling] using
    PolarizedRecompositionData.vanishingCoupling_iff_exactPotentialRecomposition (R := R)

end Core

end InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
