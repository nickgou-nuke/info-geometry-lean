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

namespace InfoGeometry.Canonical.ModularTwoStateCorrelation

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

/-- Comparison-state transported observable correlation for a relational datum. -/
@[rep_depth transport]
noncomputable def comparisonTransportCorrelation
    (R : RelationalInformationDatum (E := E))
    (A B : ObservableAlgebra E) (t : ℝ) : ℝ :=
  twoStateObservableCorrelation (E := E) R.comparisonState R.comparisonState A
    (comparisonTransportedObservable (E := E) R B t)

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
    (P : PotentialDatum (E := E)) (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    twoStateChannelCorrelation (E := E) comparison comparison X Y := by
  simp [twoStateChannelCorrelation_apply]

/-- The channel-correlation gap is the concrete comparison metric minus the reference-state channel form. -/
@[rep_depth krein]
theorem channelCorrelationGap_eq_comparisonGeneratorMetric_sub_reference
    (P : PotentialDatum (E := E)) (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    channelCorrelationGap (E := E) reference comparison X Y
      =
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      -
    channelCorrelationAtState (E := E) reference X Y := by
  simp [channelCorrelationGap, twoStateChannelCorrelation_apply, channelCorrelationAtState_apply]

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

end Core

end InfoGeometry.Canonical.ModularTwoStateCorrelation
