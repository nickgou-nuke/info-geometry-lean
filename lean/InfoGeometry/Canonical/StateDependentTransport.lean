import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Quantum.GeometricTensorOperatorLift
import Mathlib.Tactic.Abel

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.StateDependentTransport

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport

/--
State-dependent modular owner datum on the doubled real carrier.

This stores the operator seed from which the relative modular generator is
constructed at each state. The generator and all readouts remain derived.
-/
structure StateModularDatum
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  modularSeed : DoubledSpace E → (DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Paired real-doubled QGT readout attached to a state/operator pair. -/
structure StateQGTReadout
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  metric : LinearMap.BilinForm ℝ (DoubledSpace E)
  phase : LinearMap.BilinForm ℝ (DoubledSpace E)

/--
`J`-paired sheet datum for left/right modular seeds on the doubled carrier.

The pairing is imposed on the derived relative modular generators rather than on
an external spacetime field.
-/
structure JPairedStateGenerators
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  left : StateModularDatum E
  right : StateModularDatum E
  J_pairs :
    ∀ ψ : DoubledSpace E,
      relativeModularKGenerator (E := E) ((right.modularSeed ψ))
        =
      (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E)).comp
        ((relativeModularKGenerator (E := E) (left.modularSeed ψ)).comp
          (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E)))

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Constant modular owner datum. -/
def constantStateModularDatum (hMod : EndH) : StateModularDatum E where
  modularSeed := fun _ => hMod

/-- The derived relative modular generator at state `ψ`. -/
noncomputable def stateRelativeModularGenerator
    (M : StateModularDatum E) (ψ : H₂) : EndH :=
  relativeModularKGenerator (E := E) (M.modularSeed ψ)

/-- The phase-linear gauge part of the state-dependent relative modular generator. -/
noncomputable def stateGaugeGenerator
    (M : StateModularDatum E) (ψ : H₂) : EndH :=
  modularGeneratorGaugePart (E := E) (M.modularSeed ψ)

/-- The phase-antilinear source/dilation part of the state-dependent generator. -/
noncomputable def stateSourceGenerator
    (M : StateModularDatum E) (ψ : H₂) : EndH :=
  modularGeneratorScalePart (E := E) (M.modularSeed ψ)

/-- The induced derivation on observables at state `ψ`. -/
noncomputable def stateInducedDynamics
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) : EndH :=
  relativeModularDeriv (E := E) (M.modularSeed ψ) A

/-- Gauge-channel part of the state-induced dynamics. -/
noncomputable def stateGaugeDynamics
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) : EndH :=
  modularGaugeDeriv (E := E) (M.modularSeed ψ) A

/-- Source/dilation-channel part of the state-induced dynamics. -/
noncomputable def stateSourceDynamics
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) : EndH :=
  relativeModularSourceDeriv (E := E) (M.modularSeed ψ) A

/-- Operatorial modular transport of the observable seed along the state generator. -/
noncomputable def stateTransportedOperator
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.expTransport
    (A := EndH) (stateRelativeModularGenerator (E := E) M ψ) A t

/-- Symmetric operatorial readout of the state-induced dynamics. -/
noncomputable def stateQGTMetricReadout
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) :
    LinearMap.BilinForm ℝ H₂ :=
  InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
    (E := E) (stateInducedDynamics (E := E) M ψ A)

/-- `(Jε)`-sensitive phase readout of the state-induced dynamics. -/
noncomputable def stateQGTPhaseReadout
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) :
    LinearMap.BilinForm ℝ H₂ :=
  InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
    (E := E) (stateInducedDynamics (E := E) M ψ A)

@[simp] theorem stateQGTPhaseReadout_eq_metric_comp_modularComplexI
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) :
    stateQGTPhaseReadout (E := E) M ψ A
      =
    (stateQGTMetricReadout (E := E) M ψ A).compLeft
      (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)).toLinearMap := by
  rfl

/-- Bundle the metric and `(Jε)`-phase readouts into one owner surface. -/
noncomputable def stateQGTReadout
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) :
    StateQGTReadout E where
  metric := stateQGTMetricReadout (E := E) M ψ A
  phase := stateQGTPhaseReadout (E := E) M ψ A

/-- Total left/right induced dynamics on a `J`-paired state datum. -/
noncomputable def pairedStateInducedDynamics
    (P : JPairedStateGenerators E) (ψ : H₂) (A : EndH) : EndH :=
  stateInducedDynamics (E := E) P.left ψ A
    + stateInducedDynamics (E := E) P.right ψ A

/-- Total left/right gauge dynamics on a `J`-paired state datum. -/
noncomputable def pairedStateGaugeDynamics
    (P : JPairedStateGenerators E) (ψ : H₂) (A : EndH) : EndH :=
  stateGaugeDynamics (E := E) P.left ψ A
    + stateGaugeDynamics (E := E) P.right ψ A

/-- Total left/right source dynamics on a `J`-paired state datum. -/
noncomputable def pairedStateSourceDynamics
    (P : JPairedStateGenerators E) (ψ : H₂) (A : EndH) : EndH :=
  stateSourceDynamics (E := E) P.left ψ A
    + stateSourceDynamics (E := E) P.right ψ A

@[simp] theorem constantStateModularDatum_apply
    (hMod : EndH) (ψ : H₂) :
    (constantStateModularDatum (E := E) hMod).modularSeed ψ = hMod := rfl

@[simp] theorem stateRelativeModularGenerator_constant
    (hMod : EndH) (ψ : H₂) :
    stateRelativeModularGenerator (E := E)
      (constantStateModularDatum (E := E) hMod) ψ
      =
    relativeModularKGenerator (E := E) hMod := by
  rfl

@[simp] theorem stateInducedDynamics_constant
    (hMod A : EndH) (ψ : H₂) :
    stateInducedDynamics (E := E)
      (constantStateModularDatum (E := E) hMod) ψ A
      =
    relativeModularDeriv (E := E) hMod A := by
  rfl

@[simp] theorem stateQGTMetricReadout_apply
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) (u v : H₂) :
    stateQGTMetricReadout (E := E) M ψ A u v
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E) (stateInducedDynamics (E := E) M ψ A) u v := rfl

@[simp] theorem stateQGTPhaseReadout_apply
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) (u v : H₂) :
    stateQGTPhaseReadout (E := E) M ψ A u v
      =
    stateQGTMetricReadout (E := E) M ψ A
      (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E) u) v := by
  exact
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator_apply
      (E := E) (stateInducedDynamics (E := E) M ψ A) u v

/--
Local operatorial split:
the state-induced dynamics is exactly the sum of its gauge and source channels.
-/
theorem stateInducedDynamics_eq_gauge_add_source
    (M : StateModularDatum E) (ψ : H₂) (A : EndH) :
    stateInducedDynamics (E := E) M ψ A
      =
    stateGaugeDynamics (E := E) M ψ A
      +
    stateSourceDynamics (E := E) M ψ A := by
  simpa [stateInducedDynamics, stateGaugeDynamics, stateSourceDynamics] using
    (relativeModularDeriv_eq_modularGaugeDeriv_add_relativeModularSourceDeriv
      (E := E) (M.modularSeed ψ) A)

/--
Paired-sheet split:
the total left/right induced dynamics decomposes into the total gauge part plus
the total source part.
-/
theorem pairedStateInducedDynamics_eq_gauge_add_source
    (P : JPairedStateGenerators E) (ψ : H₂) (A : EndH) :
    pairedStateInducedDynamics (E := E) P ψ A
      =
    pairedStateGaugeDynamics (E := E) P ψ A
      +
    pairedStateSourceDynamics (E := E) P ψ A := by
  unfold pairedStateInducedDynamics pairedStateGaugeDynamics pairedStateSourceDynamics
  rw [stateInducedDynamics_eq_gauge_add_source (E := E) P.left ψ A,
    stateInducedDynamics_eq_gauge_add_source (E := E) P.right ψ A]
  abel

/--
If the left/right source branches cancel at a state, the total paired dynamics
reduces to the correlation-preserving gauge transport.
-/
theorem pairedSourceCancellation
    (P : JPairedStateGenerators E) (ψ : H₂) (A : EndH)
    (hCancel : pairedStateSourceDynamics (E := E) P ψ A = 0) :
    pairedStateInducedDynamics (E := E) P ψ A
      =
    pairedStateGaugeDynamics (E := E) P ψ A := by
  rw [pairedStateInducedDynamics_eq_gauge_add_source (E := E) P ψ A, hCancel]
  simp

end

end InfoGeometry.Canonical.StateDependentTransport
