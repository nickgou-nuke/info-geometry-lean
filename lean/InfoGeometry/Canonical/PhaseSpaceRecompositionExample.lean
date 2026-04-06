import InfoGeometry.Canonical.PhaseSpaceRecompositionBridge
import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Clifford.NeutralPhaseSpaceRankOne

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpaceRecompositionExample

Concrete low-dimensional example for the corrected phase-space-to-recomposition
corridor.

This file builds a genuine finite-dimensional recomposition package with:

- ambient carrier `Fin 2`,
- one-point polarized sector types,
- explicit source/target count rays `(2, 1)` and `(1, 2)`,
- nonzero sector defects `\pm log 2`,
- zero total coupling and exact recomposition,
- concrete realization of the owner-side phase transport through the maintained
  doubled corridor.
-/

namespace InfoGeometry.Canonical.PhaseSpaceRecompositionExample

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.StandardFormCore
open InfoGeometry.Canonical.RelativeModularCore
open InfoGeometry.Canonical.RelativeModularPolarizedBridge
open InfoGeometry.Canonical.RelativeModularRecomposition
open InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.PhaseSpaceRecompositionBridge
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Clifford.NeutralPhaseSpaceRankOne
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Volume.ConnesCocycle

noncomputable section

abbrev ExampleH := ℝ
abbrev AmbientIndex := Fin 2
abbrev SectorIndex := Fin 1

def sourceCounts : RelativeCounts 2 := ![(2 : ℝ), (1 : ℝ)]
def targetCounts : RelativeCounts 2 := ![(1 : ℝ), (2 : ℝ)]
def localCounts : RelativeCounts 1 := ![(1 : ℝ)]

lemma sourceCounts_pos (i : AmbientIndex) : 0 < sourceCounts i := by
  fin_cases i <;> norm_num [sourceCounts]

lemma targetCounts_pos (i : AmbientIndex) : 0 < targetCounts i := by
  fin_cases i <;> norm_num [targetCounts]

lemma localCounts_pos (i : SectorIndex) : 0 < localCounts i := by
  fin_cases i
  norm_num [localCounts]

noncomputable def sourceRay : PositiveRay AmbientIndex :=
  countRay sourceCounts sourceCounts_pos

noncomputable def targetRay : PositiveRay AmbientIndex :=
  countRay targetCounts targetCounts_pos

noncomputable def localRay : PositiveRay SectorIndex :=
  countRay localCounts localCounts_pos

theorem sourceRay_logDensity_zero :
    InfoGeometry.Canonical.PositiveRayCore.logDensity sourceRay 0 = Real.log (2 / 3 : ℝ) := by
  unfold InfoGeometry.Canonical.PositiveRayCore.logDensity sourceRay
  rw [gaugeSection_countRay_apply]
  norm_num [sourceCounts, countMass, positiveMeasureOfCounts]

theorem sourceRay_logDensity_one :
    InfoGeometry.Canonical.PositiveRayCore.logDensity sourceRay 1 = Real.log (1 / 3 : ℝ) := by
  unfold InfoGeometry.Canonical.PositiveRayCore.logDensity sourceRay
  rw [gaugeSection_countRay_apply]
  norm_num [sourceCounts, countMass, positiveMeasureOfCounts]

theorem targetRay_logDensity_zero :
    InfoGeometry.Canonical.PositiveRayCore.logDensity targetRay 0 = Real.log (1 / 3 : ℝ) := by
  unfold InfoGeometry.Canonical.PositiveRayCore.logDensity targetRay
  rw [gaugeSection_countRay_apply]
  norm_num [targetCounts, countMass, positiveMeasureOfCounts]

theorem targetRay_logDensity_one :
    InfoGeometry.Canonical.PositiveRayCore.logDensity targetRay 1 = Real.log (2 / 3 : ℝ) := by
  unfold InfoGeometry.Canonical.PositiveRayCore.logDensity targetRay
  rw [gaugeSection_countRay_apply]
  norm_num [targetCounts, countMass, positiveMeasureOfCounts]

theorem localRay_logDensity_zero :
    InfoGeometry.Canonical.PositiveRayCore.logDensity localRay 0 = 0 := by
  unfold InfoGeometry.Canonical.PositiveRayCore.logDensity localRay
  rw [gaugeSection_countRay_apply]
  norm_num [localCounts, countMass, positiveMeasureOfCounts]

noncomputable def ambientCarrier : StandardFormCarrier ExampleH where
  seed := tomitaAtomSeed
  Delta := modularSignEpsilon (E := ExampleH)
  referenceState := ⟨plusPoint (E := ExampleH) 1⟩
  modularFlow_eq_generator := rfl

noncomputable def trivialCocycle : ℝ → AlgebraEnd ExampleH := fun _ => 1

noncomputable def trivialScalarBridge :
    ScalarCocycleBridge (H := ExampleH) (ambientCarrier.seed.modularFlow) where
  toScalar :=
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := by
        intro A B
        simp }
  sigma_invariant := by
    intro s A
    rfl

theorem trivialCocycle_isCocycle :
    IsConnesCocycle ambientCarrier.seed.modularFlow trivialCocycle := by
  intro s t
  simpa [trivialCocycle] using ((ambientCarrier.seed.modularFlow s).map_one).symm

noncomputable def ambientRelativeBridge : RelativeModularBridge ExampleH AmbientIndex where
  carrier := ambientCarrier
  source := sourceRay
  target := targetRay
  cocycle := trivialCocycle
  scalarBridge := trivialScalarBridge
  isCocycle := trivialCocycle_isCocycle

def plusEmbed : SectorIndex ↪ AmbientIndex :=
  Fin.castLEEmb (by decide)

def minusEmbed : SectorIndex ↪ AmbientIndex :=
  ⟨Fin.succ, by
    intro a b h
    exact Fin.succ_injective _ h⟩

noncomputable def plusRestrictedData :
    PlusRestrictedRelativeModularData ExampleH AmbientIndex SectorIndex where
  data :=
    { carrier := ambientRelativeBridge
      embed := plusEmbed
      localSource := localRay
      localTarget := localRay
      sourceLogShift := -Real.log (2 / 3 : ℝ)
      targetLogShift := -Real.log (1 / 3 : ℝ)
      source_logDensity_eq_pullback_add_shift := by
        intro b
        fin_cases b
        change InfoGeometry.Canonical.PositiveRayCore.logDensity localRay 0 =
            InfoGeometry.Canonical.PositiveRayCore.logDensity ambientRelativeBridge.source 0
              + -Real.log (2 / 3 : ℝ)
        rw [localRay_logDensity_zero]
        change 0 = InfoGeometry.Canonical.PositiveRayCore.logDensity sourceRay 0 + -Real.log (2 / 3 : ℝ)
        rw [sourceRay_logDensity_zero]
        ring
      target_logDensity_eq_pullback_add_shift := by
        intro b
        fin_cases b
        change InfoGeometry.Canonical.PositiveRayCore.logDensity localRay 0 =
            InfoGeometry.Canonical.PositiveRayCore.logDensity ambientRelativeBridge.target 0
              + -Real.log (1 / 3 : ℝ)
        rw [localRay_logDensity_zero]
        change 0 = InfoGeometry.Canonical.PositiveRayCore.logDensity targetRay 0 + -Real.log (1 / 3 : ℝ)
        rw [targetRay_logDensity_zero]
        ring }
  lift := fun _ => plusPoint (E := ExampleH) 1
  lift_mem := by
    intro b
    fin_cases b
    simp

noncomputable def minusRestrictedData :
    MinusRestrictedRelativeModularData ExampleH AmbientIndex SectorIndex where
  data :=
    { carrier := ambientRelativeBridge
      embed := minusEmbed
      localSource := localRay
      localTarget := localRay
      sourceLogShift := -Real.log (1 / 3 : ℝ)
      targetLogShift := -Real.log (2 / 3 : ℝ)
      source_logDensity_eq_pullback_add_shift := by
        intro b
        fin_cases b
        change InfoGeometry.Canonical.PositiveRayCore.logDensity localRay 0 =
            InfoGeometry.Canonical.PositiveRayCore.logDensity ambientRelativeBridge.source 1
              + -Real.log (1 / 3 : ℝ)
        rw [localRay_logDensity_zero]
        change 0 = InfoGeometry.Canonical.PositiveRayCore.logDensity sourceRay 1 + -Real.log (1 / 3 : ℝ)
        rw [sourceRay_logDensity_one]
        ring
      target_logDensity_eq_pullback_add_shift := by
        intro b
        fin_cases b
        change InfoGeometry.Canonical.PositiveRayCore.logDensity localRay 0 =
            InfoGeometry.Canonical.PositiveRayCore.logDensity ambientRelativeBridge.target 1
              + -Real.log (2 / 3 : ℝ)
        rw [localRay_logDensity_zero]
        change 0 = InfoGeometry.Canonical.PositiveRayCore.logDensity targetRay 1 + -Real.log (2 / 3 : ℝ)
        rw [targetRay_logDensity_one]
        ring }
  lift := fun _ => minusPoint (E := ExampleH) 1
  lift_mem := by
    intro b
    fin_cases b
    simp

noncomputable def polarizedPair :
    PolarizedRelativeModularPair ExampleH AmbientIndex SectorIndex SectorIndex where
  plus := plusRestrictedData
  minus := minusRestrictedData
  sameCarrier := by
    unfold plusRestrictedData minusRestrictedData
    rfl

noncomputable def recompositionData :
    PolarizedRecompositionData ExampleH AmbientIndex SectorIndex SectorIndex where
  polarized := polarizedPair

theorem ambient_countMassShift_eq_zero :
    countMassShift sourceCounts targetCounts sourceCounts_pos targetCounts_pos = 0 := by
  rw [countMassShift_eq_neg_log_countRelativeVolumeChange]
  have hvol :
      countRelativeVolumeChange sourceCounts targetCounts sourceCounts_pos targetCounts_pos = 1 := by
    unfold countRelativeVolumeChange countMass
    norm_num [positiveMeasureOfCounts, sourceCounts, targetCounts]
  rw [hvol]
  norm_num

theorem ambient_projectiveLogDensity_zero :
    ambientRelativeBridge.projectiveLogDensity 0 = Real.log (2 : ℝ) := by
  calc
    ambientRelativeBridge.projectiveLogDensity 0
      = relativeCountLogDensity 2 sourceCounts targetCounts 0
          + countMassShift sourceCounts targetCounts sourceCounts_pos targetCounts_pos := by
            change
              InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity
                  (countRay sourceCounts sourceCounts_pos)
                  (countRay targetCounts targetCounts_pos) 0
                = relativeCountLogDensity 2 sourceCounts targetCounts 0
                    + countMassShift sourceCounts targetCounts sourceCounts_pos targetCounts_pos
            exact
              relativeLogDensity_countRay_eq_relativeCountLogDensity_add_massShift
                (n := 2) (counts := sourceCounts) (ref := targetCounts)
                (hcounts := sourceCounts_pos) (href := targetCounts_pos) (i := (0 : AmbientIndex))
    _ = Real.log (2 : ℝ) := by
          rw [ambient_countMassShift_eq_zero]
          unfold relativeCountLogDensity relativeCountDensity
          norm_num [sourceCounts, targetCounts]

theorem ambient_projectiveLogDensity_one :
    ambientRelativeBridge.projectiveLogDensity 1 = -Real.log (2 : ℝ) := by
  calc
    ambientRelativeBridge.projectiveLogDensity 1
      = relativeCountLogDensity 2 sourceCounts targetCounts 1
          + countMassShift sourceCounts targetCounts sourceCounts_pos targetCounts_pos := by
            change
              InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity
                  (countRay sourceCounts sourceCounts_pos)
                  (countRay targetCounts targetCounts_pos) 1
                = relativeCountLogDensity 2 sourceCounts targetCounts 1
                    + countMassShift sourceCounts targetCounts sourceCounts_pos targetCounts_pos
            exact
              relativeLogDensity_countRay_eq_relativeCountLogDensity_add_massShift
                (n := 2) (counts := sourceCounts) (ref := targetCounts)
                (hcounts := sourceCounts_pos) (href := targetCounts_pos) (i := (1 : AmbientIndex))
    _ = -Real.log (2 : ℝ) := by
          rw [ambient_countMassShift_eq_zero]
          unfold relativeCountLogDensity relativeCountDensity
          rw [show (sourceCounts 1 / targetCounts 1 : ℝ) = 1 / 2 by norm_num [sourceCounts, targetCounts]]
          rw [Real.log_div (by norm_num) (by norm_num)]
          rw [Real.log_one]
          ring

theorem plusLogDefect_eq_neg_log_two :
    recompositionData.plusLogDefect = -Real.log (2 : ℝ) := by
  unfold PolarizedRecompositionData.plusLogDefect recompositionData polarizedPair plusRestrictedData
  change -Real.log (2 / 3 : ℝ) - -Real.log (1 / 3 : ℝ) = -Real.log (2 : ℝ)
  rw [show (2 / 3 : ℝ) = 2 * (1 / 3 : ℝ) by norm_num]
  rw [Real.log_mul (by norm_num) (by norm_num)]
  ring

theorem minusLogDefect_eq_log_two :
    recompositionData.minusLogDefect = Real.log (2 : ℝ) := by
  unfold PolarizedRecompositionData.minusLogDefect recompositionData polarizedPair minusRestrictedData
  change -Real.log (1 / 3 : ℝ) - -Real.log (2 / 3 : ℝ) = Real.log (2 : ℝ)
  rw [show (2 / 3 : ℝ) = 2 * (1 / 3 : ℝ) by norm_num]
  rw [Real.log_mul (by norm_num) (by norm_num)]
  ring

theorem couplingLogDefect_eq_zero :
    recompositionData.couplingLogDefect = 0 := by
  rw [PolarizedRecompositionData.couplingLogDefect]
  simp [plusLogDefect_eq_neg_log_two, minusLogDefect_eq_log_two]

theorem couplingPotentialDefect_eq_zero :
    recompositionData.couplingPotentialDefect = 0 := by
  rw [PolarizedRecompositionData.couplingPotentialDefect_eq_neg_couplingLogDefect]
  rw [couplingLogDefect_eq_zero]
  norm_num

theorem exactLogRecomposition :
    recompositionData.exactLogRecomposition := by
  exact
    (PolarizedRecompositionData.vanishingCoupling_iff_exactLogRecomposition
      (R := recompositionData)).mp couplingLogDefect_eq_zero

theorem exactPotentialRecomposition :
    recompositionData.exactPotentialRecomposition := by
  exact
    (PolarizedRecompositionData.vanishingCoupling_iff_exactPotentialRecomposition
      (R := recompositionData)).mp couplingLogDefect_eq_zero

theorem generalizedMetricTwistShadow_eq_zero :
    PolarizedRecompositionData.generalizedMetricTwistShadow recompositionData = 0 := by
  rw [PolarizedRecompositionData.generalizedMetricTwistShadow_eq_couplingLogDefect]
  exact couplingLogDefect_eq_zero

theorem generalizedMetricPotentialShadow_eq_zero :
    PolarizedRecompositionData.generalizedMetricPotentialShadow recompositionData = 0 := by
  rw [PolarizedRecompositionData.generalizedMetricPotentialShadow_eq_couplingPotentialDefect]
  exact couplingPotentialDefect_eq_zero

theorem plusPhaseTransportLift_realizes_through_doubled_corridor :
    toDoubledCopyRho (E := ExampleH) dualRealEquiv.symm
        (PolarizedRecompositionData.plusPhaseTransportLift recompositionData dualRealEquiv.symm 0)
      = InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge.PolarizedRecompositionData.plusMetricTransportLift
          recompositionData 0 := by
  exact PolarizedRecompositionData.plusPhaseTransportLift_realizes_as_plusMetricTransportLift
    (R := recompositionData) (ρ := dualRealEquiv.symm) (b := 0)

theorem minusPhaseTransportLift_realizes_through_doubled_corridor :
    toDoubledCopyRho (E := ExampleH) dualRealEquiv.symm
        (PolarizedRecompositionData.minusPhaseTransportLift recompositionData dualRealEquiv.symm 0)
      = InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge.PolarizedRecompositionData.minusMetricTransportLift
          recompositionData 0 := by
  exact PolarizedRecompositionData.minusPhaseTransportLift_realizes_as_minusMetricTransportLift
    (R := recompositionData) (ρ := dualRealEquiv.symm) (b := 0)

end
