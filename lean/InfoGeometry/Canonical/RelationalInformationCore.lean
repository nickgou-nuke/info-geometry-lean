import InfoGeometry.Canonical.StateDependentTransport
import InfoGeometry.Meta.Architecture
import Mathlib.Algebra.Lie.OfAssociative

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RelationalInformationCore

Operatorial root package for relational information geometry on the doubled
carrier.

This file avoids the scalar/diagonal presentation. The primitive data are:

- the observable algebra `EndH`,
- a reference/comparison state pair on the doubled carrier,
- a state-dependent modular generator package,
- a primitive information functional,
- and its second variation on perturbation channels.

Metric, phase, and transport-obstruction readouts are derived from this
operatorial package. No background manifold, coordinate Hessian, or scalar
Fisher metric is assumed here.
-/

namespace InfoGeometry.Canonical.RelationalInformationCore

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Primitive observable algebra on the doubled operatorial carrier. -/
@[rep_depth krein]
abbrev ObservableAlgebra
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/-- Primitive perturbation channels are doubled-space endomorphisms. -/
@[rep_depth krein]
abbrev PerturbationChannel
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  ObservableAlgebra E

/--
Primitive operatorial relational datum.

The information functional is carried at the state level, while its second
variation is already packaged on the perturbation-channel module. This keeps
the root layer algebraic and avoids any coordinate Hessian surface.
-/
@[rep_depth krein]
structure RelationalInformationDatum where
  referenceState : H₂
  comparisonState : H₂
  modularData : StateModularDatum E
  informationFunctional : H₂ → ℝ
  firstVariation : H₂ → PerturbationChannel E → ℝ
  secondVariation : H₂ → LinearMap.BilinForm ℝ (PerturbationChannel E)

/-- Functional value at the reference state. -/
@[rep_depth krein]
noncomputable def referenceFunctionalValue
    (R : RelationalInformationDatum (E := E)) : ℝ :=
  R.informationFunctional R.referenceState

/-- Functional value at the comparison state. -/
@[rep_depth krein]
noncomputable def comparisonFunctionalValue
    (R : RelationalInformationDatum (E := E)) : ℝ :=
  R.informationFunctional R.comparisonState

/-- Relative functional shift from reference to comparison state. -/
@[rep_depth krein]
noncomputable def functionalShift
    (R : RelationalInformationDatum (E := E)) : ℝ :=
  comparisonFunctionalValue R - referenceFunctionalValue R

/-- Primitive second-variation form at the comparison state. -/
@[rep_depth krein]
noncomputable def comparisonGeneratorMetric
    (R : RelationalInformationDatum (E := E)) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  R.secondVariation R.comparisonState

/--
`K = Jε` acting on perturbation channels by right composition.

This is the generator-module phase axis compatible with the operatorial Berry
readout convention: the phase twist is applied to the state slot on which the
channel acts.
-/
@[rep_depth krein]
noncomputable def channelPhaseAxis :
    PerturbationChannel E →ₗ[ℝ] PerturbationChannel E where
  toFun := fun X => X.comp (modularComplexI (E := E))
  map_add' X Y := by
    exact ContinuousLinearMap.add_comp X Y (modularComplexI (E := E))
  map_smul' c X := by
    exact ContinuousLinearMap.smul_comp c X (modularComplexI (E := E))

@[rep_depth krein, simp] theorem channelPhaseAxis_apply
    (X : PerturbationChannel E) :
    channelPhaseAxis X = X.comp (modularComplexI (E := E)) :=
  rfl

@[rep_depth krein, simp] theorem channelPhaseAxis_apply_eq_comp_complex_i
    (X : PerturbationChannel E) :
    channelPhaseAxis X = X.comp (InfoGeometry.Krein.complex_i (E := E)) := by
  rw [← InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i]
  exact channelPhaseAxis_apply (E := E) X

/-- On the generator module, the induced phase axis still squares to `-Id`. -/
@[rep_depth krein]
theorem channelPhaseAxis_sq :
    channelPhaseAxis.comp channelPhaseAxis
      =
    -(LinearMap.id : PerturbationChannel E →ₗ[ℝ] PerturbationChannel E) := by
  ext X u <;>
    simp [channelPhaseAxis, LinearMap.comp_apply, ContinuousLinearMap.comp_assoc]

/-- `(Jε)`-polarized second-variation form on perturbation channels. -/
@[rep_depth krein]
noncomputable def comparisonGeneratorPhase
    (R : RelationalInformationDatum (E := E)) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  (comparisonGeneratorMetric R).compLeft channelPhaseAxis

@[rep_depth krein, simp] theorem comparisonGeneratorPhase_apply
    (R : RelationalInformationDatum (E := E))
    (X Y : PerturbationChannel E) :
    comparisonGeneratorPhase R X Y
      =
    comparisonGeneratorMetric R (channelPhaseAxis X) Y := rfl

/-- The derived relative modular generator at the comparison state. -/
@[rep_depth transport]
noncomputable def comparisonTransportGenerator
    (R : RelationalInformationDatum (E := E)) : EndH :=
  stateRelativeModularGenerator (E := E) R.modularData R.comparisonState

/-- The derived relative modular derivation on observables at the comparison state. -/
@[rep_depth transport]
noncomputable def comparisonInducedDynamics
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) : EndH :=
  stateInducedDynamics (E := E) R.modularData R.comparisonState A

/-- Gauge-sector component of the comparison-state induced dynamics. -/
@[rep_depth transport]
noncomputable def comparisonGaugeDynamics
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) : EndH :=
  stateGaugeDynamics (E := E) R.modularData R.comparisonState A

/-- Source/dilation component of the comparison-state induced dynamics. -/
@[rep_depth transport]
noncomputable def comparisonSourceDynamics
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) : EndH :=
  stateSourceDynamics (E := E) R.modularData R.comparisonState A

/-- Operatorial transport of an observable seed at the comparison state. -/
@[rep_depth transport]
noncomputable def comparisonTransportedObservable
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) (t : ℝ) : EndH :=
  stateTransportedOperator (E := E) R.modularData R.comparisonState A t

/-- Metric readout of the comparison-state induced dynamics. -/
@[rep_depth transport]
noncomputable def comparisonMetricReadout
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    LinearMap.BilinForm ℝ H₂ :=
  stateQGTMetricReadout (E := E) R.modularData R.comparisonState A

/-- `(Jε)`-phase readout of the comparison-state induced dynamics. -/
@[rep_depth transport]
noncomputable def comparisonPhaseReadout
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    LinearMap.BilinForm ℝ H₂ :=
  stateQGTPhaseReadout (E := E) R.modularData R.comparisonState A

/-- The comparison-state metric readout is the operatorial metric of the comparison dynamics. -/
@[rep_depth transport, simp] theorem comparisonMetricReadout_apply
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) (u v : H₂) :
    comparisonMetricReadout R A u v
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E) (comparisonInducedDynamics R A) u v := rfl

/-- The comparison-state phase readout is the operatorial Berry form of the comparison dynamics. -/
@[rep_depth transport, simp] theorem comparisonPhaseReadout_apply
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) (u v : H₂) :
    comparisonPhaseReadout R A u v
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
      (E := E) (comparisonInducedDynamics R A) u v := rfl

/-- The comparison-state induced dynamics splits into gauge and source channels. -/
@[rep_depth transport]
theorem comparisonInducedDynamics_eq_gauge_add_source
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonInducedDynamics R A
      =
    comparisonGaugeDynamics R A + comparisonSourceDynamics R A := by
  exact stateInducedDynamics_eq_gauge_add_source
    (E := E) R.modularData R.comparisonState A

/-- The comparison-state phase readout is the metric readout twisted by `K = Jε`. -/
@[rep_depth transport, simp] theorem comparisonPhaseReadout_eq_metric_comp_modularComplexI
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonPhaseReadout R A
      =
    (comparisonMetricReadout R A).compLeft
      (modularComplexI (E := E)).toLinearMap := by
  exact stateQGTPhaseReadout_eq_metric_comp_modularComplexI
    (E := E) R.modularData R.comparisonState A

@[rep_depth transport, simp] theorem comparisonPhaseReadout_eq_metric_comp_complex_i
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonPhaseReadout R A
      =
    (comparisonMetricReadout R A).compLeft
      (InfoGeometry.Krein.complex_i (E := E)).toLinearMap := by
  rw [← InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i]
  exact comparisonPhaseReadout_eq_metric_comp_modularComplexI (E := E) R A

/-- Inner perturbation channel generated by a doubled-space operator. -/
@[rep_depth transport]
noncomputable def perturbationDerivation
    (X : PerturbationChannel E) :
    PerturbationChannel E →ₗ[ℝ] PerturbationChannel E where
  toFun := fun A => ⁅X, A⁆
  map_add' A B := by
    simp
  map_smul' c A := by
    simp

/--
Algebraic transport obstruction for three perturbation channels.

For inner derivation channels this is the Jacobi defect, so the primitive
operator-algebraic transport is flat before additional boundary/projector
regularization is imposed.
-/
@[rep_depth transport]
noncomputable def transportObstruction
    (X Y A : PerturbationChannel E) : PerturbationChannel E :=
  ⁅X, ⁅Y, A⁆⁆ - ⁅Y, ⁅X, A⁆⁆ - ⁅⁅X, Y⁆, A⁆

/-- The primitive inner-derivation transport obstruction vanishes identically. -/
@[rep_depth transport, simp] theorem transportObstruction_eq_zero
    (X Y A : PerturbationChannel E) :
    transportObstruction X Y A = 0 := by
  have hLie :
      ⁅X, ⁅Y, A⁆⁆ - ⁅Y, ⁅X, A⁆⁆ = ⁅⁅X, Y⁆, A⁆ := by
    exact (lie_lie (x := X) (y := Y) (m := A)).symm
  calc
    transportObstruction X Y A
        = (⁅X, ⁅Y, A⁆⁆ - ⁅Y, ⁅X, A⁆⁆) - ⁅⁅X, Y⁆, A⁆ := rfl
    _ = 0 := by rw [hLie, sub_self]

end Core

end InfoGeometry.Canonical.RelationalInformationCore
