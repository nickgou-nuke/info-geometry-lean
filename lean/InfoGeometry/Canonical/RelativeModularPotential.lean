import InfoGeometry.Canonical.RelationalInformationCore
import Mathlib.Tactic.Ring

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RelativeModularPotential

Operatorial root functional for relative modular response on the doubled
carrier.

This file stays inside the noncommutative operatorial lane. It does not use a
background spacetime, coordinate derivatives, or diagonal toy operators.

The primitive data are:

- a state-dependent modular generator package,
- a continuous linear probe on the doubled observable algebra,
- the induced relative modular potential on doubled states,
- and its first response channels given by modular derivations.

The two-state comparison surface and the induced relational datum are derived
constructively from those owners.
-/

namespace InfoGeometry.Canonical.RelativeModularPotential

open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Krein

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Primitive operatorial datum for the relative modular potential. -/
@[rep_depth krein]
structure PotentialDatum where
  modularData : StateModularDatum E
  probe : EndH →L[ℝ] ℝ

/-- The primitive modular seed at state `ψ` used by the potential datum. -/
@[rep_depth transport]
noncomputable def modularSeed
    (P : PotentialDatum (E := E)) (ψ : H₂) : EndH :=
  stateModularSeed (E := E) P.modularData ψ

/-- The derived transport generator read by the potential datum at state `ψ`. -/
@[rep_depth transport]
noncomputable def transportGenerator
    (P : PotentialDatum (E := E)) (ψ : H₂) : EndH :=
  stateTransportGenerator (E := E) P.modularData ψ

/-- The statewise relative modular generator read by the potential datum. -/
@[rep_depth transport]
noncomputable def generator
    (P : PotentialDatum (E := E)) (ψ : H₂) : EndH :=
  transportGenerator (E := E) P ψ

/-- The primitive relative modular potential `Φ` at a doubled state. -/
@[rep_depth transport]
noncomputable def value
    (P : PotentialDatum (E := E)) (ψ : H₂) : ℝ :=
  P.probe (generator (E := E) P ψ)

/-- The modular derivation channel evaluated by the same probe. -/
@[rep_depth transport]
noncomputable def firstVariation
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) : ℝ :=
  P.probe (stateInducedDynamics (E := E) P.modularData ψ A)

/-- Gauge-preserving branch of the probed relative modular response. -/
@[rep_depth transport]
noncomputable def gaugeVariation
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) : ℝ :=
  P.probe (stateGaugeDynamics (E := E) P.modularData ψ A)

/-- Source/dilation branch of the probed relative modular response. -/
@[rep_depth transport]
noncomputable def sourceVariation
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) : ℝ :=
  P.probe (stateSourceDynamics (E := E) P.modularData ψ A)

/-- Two-state relative modular potential gap. -/
@[rep_depth transport]
noncomputable def twoStateGap
    (P : PotentialDatum (E := E)) (reference comparison : H₂) : ℝ :=
  value (E := E) P comparison - value (E := E) P reference

/-- Metric readout of the comparison-state induced dynamics. -/
@[rep_depth transport]
noncomputable def comparisonMetricReadout
    (P : PotentialDatum (E := E)) (comparison : H₂) (A : EndH) :
    LinearMap.BilinForm ℝ H₂ :=
  stateQGTMetricReadout (E := E) P.modularData comparison A

/-- Phase readout of the comparison-state induced dynamics. -/
@[rep_depth transport]
noncomputable def comparisonPhaseReadout
    (P : PotentialDatum (E := E)) (comparison : H₂) (A : EndH) :
    LinearMap.BilinForm ℝ H₂ :=
  stateQGTPhaseReadout (E := E) P.modularData comparison A

/-- The comparison-state metric readout is the operatorial metric of the induced dynamics. -/
@[rep_depth transport, simp] theorem comparisonMetricReadout_apply
    (P : PotentialDatum (E := E)) (comparison : H₂) (A : EndH) (u v : H₂) :
    comparisonMetricReadout (E := E) P comparison A u v
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E) (stateInducedDynamics (E := E) P.modularData comparison A) u v := rfl

/-- The comparison-state phase readout is the operatorial Berry form of the induced dynamics. -/
@[rep_depth transport, simp] theorem comparisonPhaseReadout_apply
    (P : PotentialDatum (E := E)) (comparison : H₂) (A : EndH) (u v : H₂) :
    comparisonPhaseReadout (E := E) P comparison A u v
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
      (E := E) (stateInducedDynamics (E := E) P.modularData comparison A) u v := rfl

/-- Channel bilinear form induced by evaluation on a fixed doubled state. -/
@[rep_depth krein]
noncomputable def channelCorrelationAtState
    (ψ : H₂) : LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  LinearMap.mk₂ ℝ
    (fun X Y => ⟪X ψ, Y ψ⟫_ℝ)
    (by
      intro X₁ X₂ Y
      simp [inner_add_left])
    (by
      intro c X Y
      simp [real_inner_smul_left]
      ring)
    (by
      intro X Y₁ Y₂
      simp [inner_add_right])
    (by
      intro c X Y
      simp [real_inner_smul_right]
      ring)

/-- Primitive comparison-state channel metric induced directly by evaluation on that state. -/
@[rep_depth krein]
noncomputable def comparisonStateGeneratorMetric
    (comparison : H₂) : LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  channelCorrelationAtState (E := E) comparison

/-- Primitive `(Jε)`-phase form on perturbation channels at the comparison state. -/
@[rep_depth krein]
noncomputable def comparisonStateGeneratorPhase
    (comparison : H₂) : LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  (comparisonStateGeneratorMetric (E := E) comparison).compLeft channelPhaseAxis

/-- Construct the abstract relational datum from the primitive potential datum. -/
@[rep_depth transport]
noncomputable def toRelationalInformationDatum
    (P : PotentialDatum (E := E)) (reference comparison : H₂) :
    RelationalInformationDatum (E := E) where
  referenceState := reference
  comparisonState := comparison
  modularData := P.modularData
  informationFunctional := value (E := E) P
  firstVariation := firstVariation (E := E) P
  secondVariation := fun ψ => channelCorrelationAtState (E := E) ψ

@[rep_depth transport, simp] theorem generator_eq
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    generator (E := E) P ψ = stateRelativeModularGenerator (E := E) P.modularData ψ := rfl

@[rep_depth transport, simp] theorem modularSeed_eq
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    modularSeed (E := E) P ψ = P.modularData.modularSeed ψ := rfl

@[rep_depth transport, simp] theorem transportGenerator_eq
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    transportGenerator (E := E) P ψ
      =
    stateRelativeModularGenerator (E := E) P.modularData ψ := rfl

@[rep_depth transport, simp] theorem value_eq_probe_generator
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    value (E := E) P ψ = P.probe (generator (E := E) P ψ) := rfl

@[rep_depth transport]
theorem firstVariation_eq_gauge_add_source
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    firstVariation (E := E) P ψ A
      =
    gaugeVariation (E := E) P ψ A + sourceVariation (E := E) P ψ A := by
  unfold firstVariation gaugeVariation sourceVariation
  rw [stateInducedDynamics_eq_gauge_add_source (E := E) P.modularData ψ A]
  simp

@[rep_depth transport, simp] theorem comparisonPhaseReadout_eq_metric_comp_complex_i
    (P : PotentialDatum (E := E)) (comparison : H₂) (A : EndH) :
    comparisonPhaseReadout (E := E) P comparison A
      =
    (comparisonMetricReadout (E := E) P comparison A).compLeft
      (InfoGeometry.Krein.complex_i (E := E)).toLinearMap := by
  simpa [comparisonPhaseReadout, comparisonMetricReadout] using
    (stateQGTPhaseReadout_eq_metric_comp_complex_i
      (E := E) P.modularData comparison A)

@[rep_depth transport, simp] theorem comparisonPhaseReadout_eq_metric_comp_modularComplexI
    (P : PotentialDatum (E := E)) (comparison : H₂) (A : EndH) :
    comparisonPhaseReadout (E := E) P comparison A
      =
    (comparisonMetricReadout (E := E) P comparison A).compLeft
      (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)).toLinearMap := by
  simpa [comparisonPhaseReadout, comparisonMetricReadout] using
    (stateQGTPhaseReadout_eq_metric_comp_modularComplexI
      (E := E) P.modularData comparison A)

@[rep_depth krein, simp] theorem channelCorrelationAtState_apply
    (ψ : H₂) (X Y : PerturbationChannel E) :
    channelCorrelationAtState (E := E) ψ X Y = ⟪X ψ, Y ψ⟫_ℝ := rfl

@[rep_depth krein, simp] theorem comparisonStateGeneratorMetric_apply
    (comparison : H₂) (X Y : PerturbationChannel E) :
    comparisonStateGeneratorMetric (E := E) comparison X Y
      =
    ⟪X comparison, Y comparison⟫_ℝ := rfl

@[rep_depth krein, simp] theorem comparisonStateGeneratorPhase_apply_eq_comp_complex_i
    (comparison : H₂) (X Y : PerturbationChannel E) :
    comparisonStateGeneratorPhase (E := E) comparison X Y
      =
    ⟪(X.comp (InfoGeometry.Krein.complex_i (E := E))) comparison,
      Y comparison⟫_ℝ := by
  simp [comparisonStateGeneratorPhase, comparisonStateGeneratorMetric,
    channelPhaseAxis]

@[rep_depth krein, simp] theorem comparisonStateGeneratorPhase_apply
    (comparison : H₂) (X Y : PerturbationChannel E) :
    comparisonStateGeneratorPhase (E := E) comparison X Y
      =
    ⟪(X.comp (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E))) comparison,
      Y comparison⟫_ℝ := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    (comparisonStateGeneratorPhase_apply_eq_comp_complex_i
      (E := E) comparison X Y)

@[rep_depth transport, simp] theorem toRelationalInformationDatum_informationFunctional
    (P : PotentialDatum (E := E)) (reference comparison ψ : H₂) :
    (toRelationalInformationDatum (E := E) P reference comparison).informationFunctional ψ
      =
    value (E := E) P ψ := rfl

@[rep_depth transport, simp] theorem toRelationalInformationDatum_firstVariation
    (P : PotentialDatum (E := E)) (reference comparison ψ : H₂) (A : EndH) :
    (toRelationalInformationDatum (E := E) P reference comparison).firstVariation ψ A
      =
    firstVariation (E := E) P ψ A := rfl

@[rep_depth transport, simp] theorem toRelationalInformationDatum_functionalShift
    (P : PotentialDatum (E := E)) (reference comparison : H₂) :
    functionalShift (toRelationalInformationDatum (E := E) P reference comparison)
      =
    twoStateGap (E := E) P reference comparison := by
  rfl

@[rep_depth transport, simp] theorem toRelationalInformationDatum_comparisonGeneratorMetric_apply
    (P : PotentialDatum (E := E)) (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    ⟪X comparison, Y comparison⟫_ℝ := by
  rfl

@[rep_depth transport, simp] theorem toRelationalInformationDatum_comparisonGeneratorPhase_apply
    (P : PotentialDatum (E := E)) (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    ⟪(X.comp (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E))) comparison,
      Y comparison⟫_ℝ := by
  rw [comparisonGeneratorPhase_apply]
  rw [toRelationalInformationDatum_comparisonGeneratorMetric_apply
    (E := E) P reference comparison (channelPhaseAxis (E := E) X) Y]
  simp [channelPhaseAxis_apply]

@[rep_depth transport, simp] theorem toRelationalInformationDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i
    (P : PotentialDatum (E := E)) (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    ⟪(X.comp (InfoGeometry.Krein.complex_i (E := E))) comparison,
      Y comparison⟫_ℝ := by
  rw [comparisonGeneratorPhase_apply]
  rw [toRelationalInformationDatum_comparisonGeneratorMetric_apply
    (E := E) P reference comparison (channelPhaseAxis (E := E) X) Y]
  simp [channelPhaseAxis_apply,
    InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i]

attribute [deprecated comparisonStateGeneratorPhase_apply_eq_comp_complex_i (since := "2026-04-11")]
  comparisonStateGeneratorPhase_apply

attribute [deprecated toRelationalInformationDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i
  (since := "2026-04-11")]
  toRelationalInformationDatum_comparisonGeneratorPhase_apply

end Core

end InfoGeometry.Canonical.RelativeModularPotential
