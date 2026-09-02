/- SPDX-License-Identifier: Apache-2.0 -/

/-
# Dikin--lambda--braid--Hestenes--Krein closure

This is an integration layer over existing owner modules.  It does not identify
Dikin geometry with Cauchy analyticity and does not introduce a topological
bundle or analytic holonomy theorem.  It collects the certified finite
readouts already owned by the repository.
-/

import InfoGeometry.Canonical.DikinMetriplecticCapstone
import InfoGeometry.Canonical.BKMDriftMetric
import InfoGeometry.Categorical.LambdaBraidHestenesKreinBridge

noncomputable section

namespace InfoGeometry.Canonical.DikinLambdaBraidHestenesKreinClosure

open InfoGeometry.Canonical.DikinMetriplecticCapstone
open InfoGeometry.SymmetricDomains.DikinMetriplectic
open InfoGeometry.Canonical.BKMDriftMetric
open InfoGeometry.Categorical.LambdaBraidHestenesKreinBridge

universe u

/-- Explicit inputs for the cross-lane closure theorem. -/
structure ClosureData
    (Weight Tangent State : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  compiled : CompiledTheoryBridge.{u}
  tube : TubeCoordinate
  v1 : ℝ
  v2 : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_lt_one : radius < 1
  dikin_bound : dikinQuadraticForm tube v1 v2 ≤ radius ^ 2
  surprisal_coordinate : ℝ
  metriplectic_state : MetriplecticState
  bkmFusion : ConnesBKMDriftFusion Weight Tangent State
  bkmCalibration : DriftIntensityCalibratesConnesBKM bkmFusion
  gaugeFixed : IsGaugeFixedBKMDriftMass bkmFusion.metric
  gaugeNonnegative : HasNonnegativeBKMGauge bkmFusion.metric
  bkm_state : State

/-- The certified readouts supplied by ClosureData. -/
structure CertifiedReadout
    (D : ClosureData Weight Tangent State) where
  dag : (lambdaToCausalNet D.compiled.term).IsDAG
  negativeGrammar :
    causalNetToPolarity D.compiled.net = Polarity.negative
  braidStage :
    ∀ n : ℕ,
      stageInjection D.compiled.braidDiagram n ≫
          descendedEndomorphism D.compiled.braidDiagram
            D.compiled.braidData.braid1 =
        D.compiled.braidData.braid1.app n ≫
          stageInjection D.compiled.braidDiagram n
  hestenesStage :
    ∀ n m : ℕ, ∀ x : DoubledSpace (D.compiled.hestenesCone.Base n),
      D.compiled.analyticFamily.colimitReadout (n + m)
          (FilteredPhaseCone.bondIterate
            D.compiled.hestenesCone.toFilteredPhaseCone n m x) =
        D.compiled.analyticFamily.colimitReadout n x
  dikinInterior :
    0 < D.tube.y1 + D.v1 ∧ 0 < D.tube.y2 + D.v2
  barrierIdentity :
    universalLogBarrier D.tube =
      - Real.log (coneCharacteristicPoly D.tube)
  hessianDeterminant :
    (coneHessianMetric D.tube).det =
      1 / (coneCharacteristicPoly D.tube) ^ 2
  surprisalNonnegative :
    0 ≤ Real.exp (-D.surprisal_coordinate) - 1 +
      D.surprisal_coordinate
  dissipationNonnegative :
    0 ≤ D.metriplectic_state.dissipation_rate
  bkmDriftNonnegative :
    0 ≤ D.bkmFusion.metric.driftIntensity D.bkm_state
  bkmMassNonnegative :
    0 ≤ D.bkmFusion.metric.physicalMass D.bkm_state
  bkmMassWeylInvariant :
    ∀ (c : ℝ), c ≠ 0 →
      D.bkmFusion.metric.physicalMass
        (D.bkmFusion.metric.scale c D.bkm_state) =
      D.bkmFusion.metric.physicalMass D.bkm_state

namespace CertifiedReadout

variable {Weight Tangent State : Type*}
variable [AddCommGroup Tangent] [Module ℝ Tangent]

/-- Construct every readout from the owner theorems. -/
def of (D : ClosureData Weight Tangent State) : CertifiedReadout D where
  dag := D.compiled.lambda_lane_dag
  negativeGrammar := D.compiled.negative_grammar_lane
  braidStage := by
    intro n
    exact (D.compiled.braid_lane).1 n
  hestenesStage := D.compiled.hestenes_lane
  dikinInterior :=
    (verification_capstone D.tube D.v1 D.v2 D.radius
      D.radius_nonneg D.radius_lt_one D.dikin_bound
      D.surprisal_coordinate D.metriplectic_state).2.2.1
  barrierIdentity :=
    (verification_capstone D.tube D.v1 D.v2 D.radius
      D.radius_nonneg D.radius_lt_one D.dikin_bound
      D.surprisal_coordinate D.metriplectic_state).1
  hessianDeterminant :=
    (verification_capstone D.tube D.v1 D.v2 D.radius
      D.radius_nonneg D.radius_lt_one D.dikin_bound
      D.surprisal_coordinate D.metriplectic_state).2.1
  surprisalNonnegative :=
    (verification_capstone D.tube D.v1 D.v2 D.radius
      D.radius_nonneg D.radius_lt_one D.dikin_bound
      D.surprisal_coordinate D.metriplectic_state).2.2.2.1
  dissipationNonnegative :=
    (verification_capstone D.tube D.v1 D.v2 D.radius
      D.radius_nonneg D.radius_lt_one D.dikin_bound
      D.surprisal_coordinate D.metriplectic_state).2.2.2.2
  bkmDriftNonnegative :=
    D.bkmFusion.driftIntensity_nonnegative D.bkmCalibration D.bkm_state
  bkmMassNonnegative :=
    D.bkmFusion.physicalMass_nonnegative D.bkmCalibration
      D.gaugeFixed D.gaugeNonnegative D.bkm_state
  bkmMassWeylInvariant := by
    intro c hc
    exact D.bkmFusion.metric.physicalMass_weylInvariant
      D.gaugeFixed
      (fun s => D.bkmFusion.driftIntensity_nonnegative
        D.bkmCalibration s)
      (fun s => D.gaugeNonnegative s) c D.bkm_state hc

end CertifiedReadout

/-- The audited cross-lane closure readout. -/
def certifiedReadout
    (D : ClosureData Weight Tangent State) : CertifiedReadout D :=
  CertifiedReadout.of D

/-- The principal conjunction of the audited closure laws. -/
theorem certified_closure
    (D : ClosureData Weight Tangent State) :
    (lambdaToCausalNet D.compiled.term).IsDAG ∧
    causalNetToPolarity D.compiled.net = Polarity.negative ∧
    (∀ n : ℕ,
      stageInjection D.compiled.braidDiagram n ≫
          descendedEndomorphism D.compiled.braidDiagram
            D.compiled.braidData.braid1 =
        D.compiled.braidData.braid1.app n ≫
          stageInjection D.compiled.braidDiagram n) ∧
    (∀ n m : ℕ, ∀ x : DoubledSpace (D.compiled.hestenesCone.Base n),
      D.compiled.analyticFamily.colimitReadout (n + m)
          (FilteredPhaseCone.bondIterate
            D.compiled.hestenesCone.toFilteredPhaseCone n m x) =
        D.compiled.analyticFamily.colimitReadout n x) ∧
    (0 < D.tube.y1 + D.v1 ∧ 0 < D.tube.y2 + D.v2) ∧
    0 ≤ D.bkmFusion.metric.physicalMass D.bkm_state := by
  let R := certifiedReadout D
  exact ⟨R.dag, R.negativeGrammar, R.braidStage,
    R.hestenesStage, R.dikinInterior, R.bkmMassNonnegative⟩

end InfoGeometry.Canonical.DikinLambdaBraidHestenesKreinClosure
