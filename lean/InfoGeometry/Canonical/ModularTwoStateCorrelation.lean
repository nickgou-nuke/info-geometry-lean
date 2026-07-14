import InfoGeometry.Canonical.OnsagerReciprocity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModularTwoStateCorrelation

Operatorial two-state / two-channel correlation layer on the doubled carrier.

This file stays in the noncommutative operatorial lane. It introduces:

- raw two-state observable correlations,
- raw two-state perturbation-channel correlations,
- reference/comparison correlation gaps,
- and transported observable correlations along the derived modular flow.

No spacetime points or background time coordinates are used. The only transport
parameter present here is the internal modular/Bogoliubov flow parameter already
carried by the operatorial transport layer.
-/

namespace ModularTwoStateCorrelation

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Raw two-state observable correlation on the doubled carrier. -/
@[rep_depth krein]
noncomputable def twoStateObservableCorrelation
    (reference comparison : H₂) (A B : EndH) : ℝ :=
  ⟪A reference, B comparison⟫_ℝ

/-- Raw two-state perturbation-channel correlation on the doubled carrier. -/
@[rep_depth krein]
noncomputable def twoStateChannelCorrelation
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) : ℝ :=
  twoStateObservableCorrelation (E := E) reference comparison X Y

/-- Reference/comparison observable-correlation gap. -/
@[rep_depth krein]
noncomputable def observableCorrelationGap
    (reference comparison : H₂) (A B : EndH) : ℝ :=
  twoStateObservableCorrelation (E := E) comparison comparison A B
    -
  twoStateObservableCorrelation (E := E) reference reference A B

/-- Reference/comparison channel-correlation gap. -/
@[rep_depth krein]
noncomputable def channelCorrelationGap
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) : ℝ :=
  twoStateChannelCorrelation (E := E) comparison comparison X Y
    -
  twoStateChannelCorrelation (E := E) reference reference X Y

/-- Transported observable correlation `⟪A ψ, α_t(B) ψ⟫` at a fixed doubled state. -/
@[rep_depth transport]
noncomputable def stateTransportCorrelation
    (M : StateModularDatum E) (ψ : H₂) (A B : EndH) (t : ℝ) : ℝ :=
  twoStateObservableCorrelation (E := E) ψ ψ A
    (stateTransportedOperator (E := E) M ψ B t)

/-- Transported `K = Jε`-shifted perturbation-channel correlation at a fixed doubled state. -/
@[rep_depth transport]
noncomputable def stateTransportPhaseShiftedChannelCorrelation
    (M : StateModularDatum E) (ψ : H₂)
    (X Y : PerturbationChannel E) (t : ℝ) : ℝ :=
  twoStateObservableCorrelation (E := E) ψ ψ
    (channelPhaseAxis (E := E) X)
    (stateTransportedOperator (E := E) M ψ Y t)

/-- Comparison-state transported observable correlation for a relational datum. -/
@[rep_depth transport]
noncomputable def comparisonTransportCorrelation
    (R : RelationalInformationDatum (E := E))
    (A B : ObservableAlgebra E) (t : ℝ) : ℝ :=
  twoStateObservableCorrelation (E := E) R.comparisonState R.comparisonState A
    (comparisonTransportedObservable (E := E) R B t)

/-- Comparison-state transported `K = Jε`-shifted perturbation-channel correlation. -/
@[rep_depth transport]
noncomputable def comparisonTransportPhaseShiftedChannelCorrelation
    (R : RelationalInformationDatum (E := E))
    (X Y : PerturbationChannel E) (t : ℝ) : ℝ :=
  stateTransportPhaseShiftedChannelCorrelation (E := E)
    R.modularData R.comparisonState X Y t

section

omit [CompleteSpace E]

@[rep_depth krein, simp] theorem twoStateObservableCorrelation_apply
    (reference comparison : H₂) (A B : EndH) :
    twoStateObservableCorrelation (E := E) reference comparison A B
      =
    ⟪A reference, B comparison⟫_ℝ := rfl

end

@[rep_depth krein, simp] theorem twoStateChannelCorrelation_apply
    (reference comparison : H₂) (X Y : PerturbationChannel E) :
    twoStateChannelCorrelation (E := E) reference comparison X Y
      =
    ⟪X reference, Y comparison⟫_ℝ := rfl

section

omit [CompleteSpace E]

/-- Swapping state and observable slots flips a two-state observable correlation by real symmetry. -/
@[rep_depth krein]
theorem twoStateObservableCorrelation_swap
    (reference comparison : H₂) (A B : EndH) :
    twoStateObservableCorrelation (E := E) reference comparison A B
      =
    twoStateObservableCorrelation (E := E) comparison reference B A := by
  simp [twoStateObservableCorrelation_apply, real_inner_comm]

end

/-- Swapping state and channel slots flips a two-state channel correlation by real symmetry. -/
@[rep_depth krein]
theorem twoStateChannelCorrelation_swap
    (reference comparison : H₂) (X Y : PerturbationChannel E) :
    twoStateChannelCorrelation (E := E) reference comparison X Y
      =
    twoStateChannelCorrelation (E := E) comparison reference Y X := by
  simp [twoStateChannelCorrelation_apply, real_inner_comm]

/-- Same-state channel correlation reduces to the primitive statewise channel form. -/
@[rep_depth krein]
theorem twoStateChannelCorrelation_self_eq_channelCorrelationAtState
    (ψ : H₂) (X Y : PerturbationChannel E) :
    twoStateChannelCorrelation (E := E) ψ ψ X Y
      =
    channelCorrelationAtState (E := E) ψ X Y := by
  rfl

/-- Same-state channel correlation also reduces to the abstract comparison-state generator metric. -/
@[rep_depth krein]
theorem comparisonGeneratorMetric_eq_twoStateChannelCorrelation_self
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonStateGeneratorMetric comparison X Y
      =
    twoStateChannelCorrelation (E := E) comparison comparison X Y := by
  simp [comparisonStateGeneratorMetric_apply, twoStateChannelCorrelation_apply]

/-- The channel-correlation gap is the concrete comparison metric minus the reference-state channel form. -/
@[rep_depth krein]
theorem channelCorrelationGap_eq_comparisonGeneratorMetric_sub_reference
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    channelCorrelationGap (E := E) reference comparison X Y
      =
    comparisonStateGeneratorMetric comparison X Y
      -
    channelCorrelationAtState (E := E) reference X Y := by
  simp [channelCorrelationGap, comparisonStateGeneratorMetric_apply,
    twoStateChannelCorrelation_apply, channelCorrelationAtState_apply]

section

omit [CompleteSpace E]

/-- Observable-correlation gap is symmetric under swapping the observable seeds. -/
@[rep_depth krein]
theorem observableCorrelationGap_swap
    (reference comparison : H₂) (A B : EndH) :
    observableCorrelationGap (E := E) reference comparison A B
      =
    observableCorrelationGap (E := E) reference comparison B A := by
  unfold observableCorrelationGap
  simp [twoStateObservableCorrelation_apply, real_inner_comm]

end

/-- Channel-correlation gap is symmetric under swapping the perturbation channels. -/
@[rep_depth krein]
theorem channelCorrelationGap_swap
    (reference comparison : H₂) (X Y : PerturbationChannel E) :
    channelCorrelationGap (E := E) reference comparison X Y
      =
    channelCorrelationGap (E := E) reference comparison Y X := by
  unfold channelCorrelationGap
  simp [twoStateChannelCorrelation_apply, real_inner_comm]

/-- The derived state transport is trivial at `t = 0`. -/
@[rep_depth transport, simp]
theorem stateTransportedOperator_zero
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) :
    stateTransportedOperator (E := E) M ψ A 0 = A := by
  simp [stateTransportedOperator, InfoGeometry.Canonical.expTransport]

/-- The comparison-state transported observable is trivial at `t = 0`. -/
@[rep_depth transport, simp]
theorem comparisonTransportedObservable_zero
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonTransportedObservable (E := E) R A 0 = A := by
  simp [comparisonTransportedObservable]

/-- At `t = 0`, the state transport correlation reduces to the raw same-state observable correlation. -/
@[rep_depth transport, simp]
theorem stateTransportCorrelation_zero
    (M : StateModularDatum E) (ψ : H₂) (A B : EndH) :
    stateTransportCorrelation (E := E) M ψ A B 0
      =
    twoStateObservableCorrelation (E := E) ψ ψ A B := by
  simp [stateTransportCorrelation]

/-- At `t = 0`, the transported `K = Jε`-shifted channel correlation reduces to the raw same-state phase-shifted correlation. -/
@[rep_depth transport, simp]
theorem stateTransportPhaseShiftedChannelCorrelation_zero
    (M : StateModularDatum E) (ψ : H₂)
    (X Y : PerturbationChannel E) :
    stateTransportPhaseShiftedChannelCorrelation (E := E) M ψ X Y 0
      =
    twoStateObservableCorrelation (E := E) ψ ψ
      (channelPhaseAxis (E := E) X) Y := by
  simp [stateTransportPhaseShiftedChannelCorrelation]

/-- At `t = 0`, the comparison transport correlation reduces to the raw comparison-state observable correlation. -/
@[rep_depth transport, simp]
theorem comparisonTransportCorrelation_zero
    (R : RelationalInformationDatum (E := E))
    (A B : ObservableAlgebra E) :
    comparisonTransportCorrelation (E := E) R A B 0
      =
    twoStateObservableCorrelation (E := E) R.comparisonState R.comparisonState A B := by
  simp [comparisonTransportCorrelation]

/-- The comparison transport correlation is the comparison-state specialization of the raw state transport correlation. -/
@[rep_depth transport]
theorem comparisonTransportCorrelation_eq_stateTransportCorrelation
    (R : RelationalInformationDatum (E := E))
    (A B : ObservableAlgebra E) (t : ℝ) :
    comparisonTransportCorrelation (E := E) R A B t
      =
    stateTransportCorrelation (E := E) R.modularData R.comparisonState A B t := by
  rfl

/-- The comparison transported `K = Jε`-shifted channel correlation is the comparison-state specialization of the raw state transport phase correlation. -/
@[rep_depth transport]
theorem comparisonTransportPhaseShiftedChannelCorrelation_eq_stateTransportPhaseShiftedChannelCorrelation
    (R : RelationalInformationDatum (E := E))
    (X Y : PerturbationChannel E) (t : ℝ) :
    comparisonTransportPhaseShiftedChannelCorrelation (E := E) R X Y t
      =
    stateTransportPhaseShiftedChannelCorrelation (E := E)
      R.modularData R.comparisonState X Y t := by
  rfl

/-- At `t = 0`, the comparison transported `K = Jε`-shifted channel correlation reduces to the raw comparison-state phase-shifted correlation. -/
@[rep_depth transport, simp]
theorem comparisonTransportPhaseShiftedChannelCorrelation_zero
    (R : RelationalInformationDatum (E := E))
    (X Y : PerturbationChannel E) :
    comparisonTransportPhaseShiftedChannelCorrelation (E := E) R X Y 0
      =
    twoStateObservableCorrelation (E := E)
      R.comparisonState R.comparisonState
      (channelPhaseAxis (E := E) X) Y := by
  simp [comparisonTransportPhaseShiftedChannelCorrelation]

/--
Infinitesimal transport law for the `K = Jε`-shifted channel correlation:
the derivative at `t = 0` is the state-QGT metric readout of the induced
dynamics, evaluated on the phase-shifted probe vector.
-/
@[rep_depth transport]
theorem hasDerivAt_stateTransportPhaseShiftedChannelCorrelation_at_zero
    (M : StateModularDatum E) (ψ : H₂)
    (X Y : PerturbationChannel E) :
    HasDerivAt
      (fun t =>
        stateTransportPhaseShiftedChannelCorrelation (E := E) M ψ X Y t)
      ((stateQGTMetricReadout (E := E) M ψ Y) ψ
        ((channelPhaseAxis (E := E) X) ψ))
      0 := by
  let ω : EndH →L[ℝ] ℝ :=
    (innerSL ℝ ((channelPhaseAxis (E := E) X) ψ)).comp
      (ContinuousLinearMap.apply ℝ H₂ ψ)
  have hω :
      HasDerivAt (fun _ : ℝ => ω) (0 : EndH →L[ℝ] ℝ) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := ω))
  have hExp :
      HasDerivAt
        (fun t : ℝ => stateTransportedOperator (E := E) M ψ Y t)
        (stateInducedDynamics (E := E) M ψ Y)
        0 := by
    simpa [stateTransportedOperator, stateInducedDynamics] using
      (InfoGeometry.Canonical.hasDerivAt_expTransport_at_zero
        (A := EndH)
        (stateRelativeModularGenerator (E := E) M ψ)
        Y)
  have hMain :
      HasDerivAt
        (fun t : ℝ =>
          stateTransportPhaseShiftedChannelCorrelation (E := E) M ψ X Y t)
        (ω (stateInducedDynamics (E := E) M ψ Y))
        0 := by
    have hApply :
        HasDerivAt
          (fun t : ℝ =>
            (fun _ : ℝ => ω) t
              (stateTransportedOperator (E := E) M ψ Y t))
          ((0 : EndH →L[ℝ] ℝ)
            (stateTransportedOperator (E := E) M ψ Y 0)
            + ω (stateInducedDynamics (E := E) M ψ Y))
          0 :=
      hω.clm_apply hExp
    simpa [stateTransportPhaseShiftedChannelCorrelation, ω,
      twoStateObservableCorrelation_apply, real_inner_comm] using hApply
  have hωEval :
      ω (stateInducedDynamics (E := E) M ψ Y)
        =
      (stateQGTMetricReadout (E := E) M ψ Y) ψ
        ((channelPhaseAxis (E := E) X) ψ) := by
    simp [ω, stateQGTMetricReadout_apply,
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_apply,
      real_inner_comm]
  exact hωEval ▸ hMain

/-- Derivative form of the infinitesimal transport law for the `K = Jε`-shifted channel correlation. -/
@[rep_depth transport]
theorem deriv_stateTransportPhaseShiftedChannelCorrelation_at_zero_eq_stateQGTMetricReadout
    (M : StateModularDatum E) (ψ : H₂)
    (X Y : PerturbationChannel E) :
    deriv
      (fun t => stateTransportPhaseShiftedChannelCorrelation (E := E) M ψ X Y t)
      0
      =
    (stateQGTMetricReadout (E := E) M ψ Y) ψ
      ((channelPhaseAxis (E := E) X) ψ) := by
  exact
    (hasDerivAt_stateTransportPhaseShiftedChannelCorrelation_at_zero
      (E := E) M ψ X Y).deriv

/--
Comparison-state specialization of the infinitesimal `K = Jε`-shifted transport
law: the derivative at `t = 0` is the comparison metric readout evaluated on
the phase-shifted probe vector.
-/
@[rep_depth transport]
theorem deriv_comparisonTransportPhaseShiftedChannelCorrelation_at_zero_eq_comparisonMetricReadout
    (R : RelationalInformationDatum (E := E))
    (X Y : PerturbationChannel E) :
    deriv
      (fun t => comparisonTransportPhaseShiftedChannelCorrelation (E := E) R X Y t)
      0
      =
    comparisonMetricReadout R Y
      R.comparisonState
      ((channelPhaseAxis (E := E) X) R.comparisonState) := by
  simpa [comparisonTransportPhaseShiftedChannelCorrelation]
    using
      deriv_stateTransportPhaseShiftedChannelCorrelation_at_zero_eq_stateQGTMetricReadout
        (E := E) R.modularData R.comparisonState X Y

end Core

end ModularTwoStateCorrelation
