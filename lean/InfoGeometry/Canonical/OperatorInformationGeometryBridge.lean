import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.OperatorInformationGeometryBridge

Carrier layer for operator information geometry.

This file intentionally contains no arbitrary `Prop` law fields.  It only names
the local real-algebraic data channels that downstream owner modules may connect
to already-proved theorem surfaces.

The discipline is:

* definitions and carriers may live here,
* actual algebra/analysis laws must be imported from their proving modules,
* no Type III, Araki, Takesaki, ergodic, or chart theorem is asserted by witness
  fields in this dictionary.
-/

namespace InfoGeometry.Canonical.OperatorInformationGeometryBridge

/--
Carrier for operator-information geometry.

This is a naming/dictionary object only.  The fields are the channels:
modular flow, relative-entropy/KL readout, conditional-expectation/update, and
ergodic/macroscopic projection.
-/
structure OperatorInformationGeometryCarrier
    (Alg State Value : Type*) where
  /-- Modular/Tomita flow or a repo-local bounded surrogate. -/
  modularFlow : ℝ → Alg → Alg

  /-- Relative entropy / KL / Araki-style readout channel. -/
  relativeEntropy : State → State → Value

  /-- Noncommutative Bayesian update channel, e.g. conditional expectation. -/
  conditionalExpectation : Alg → Alg

  /-- Ergodic/macroscopic projection channel. -/
  ergodicProjection : Alg → Alg

namespace OperatorInformationGeometryCarrier

variable {Alg State Value : Type*}
variable (G : OperatorInformationGeometryCarrier Alg State Value)

/-- Definitional readback for modular flow. -/
@[rep_depth operator]
theorem modularFlow_apply (t : ℝ) (A : Alg) :
    G.modularFlow t A = G.modularFlow t A := rfl

/-- Definitional readback for relative entropy. -/
@[rep_depth operator]
theorem relativeEntropy_apply (ρ σ : State) :
    G.relativeEntropy ρ σ = G.relativeEntropy ρ σ := rfl

/-- Definitional readback for conditional expectation/update. -/
@[rep_depth operator]
theorem conditionalExpectation_apply (A : Alg) :
    G.conditionalExpectation A = G.conditionalExpectation A := rfl

/-- Definitional readback for ergodic/macroscopic projection. -/
@[rep_depth operator]
theorem ergodicProjection_apply (A : Alg) :
    G.ergodicProjection A = G.ergodicProjection A := rfl

end OperatorInformationGeometryCarrier

/--
Carrier for modular Bayesian/update language.

No Takesaki theorem is asserted here.  Modules that prove modular invariance or
conditional-expectation laws must own those theorems directly.
-/
structure ModularBayesianUpdateCarrier
    (Alg : Type*) where
  modularFlow : ℝ → Alg → Alg
  update : Alg → Alg

namespace ModularBayesianUpdateCarrier

variable {Alg : Type*}
variable (B : ModularBayesianUpdateCarrier Alg)

@[rep_depth operator]
theorem modularFlow_apply (t : ℝ) (A : Alg) :
    B.modularFlow t A = B.modularFlow t A := rfl

@[rep_depth operator]
theorem update_apply (A : Alg) :
    B.update A = B.update A := rfl

end ModularBayesianUpdateCarrier

/--
Carrier for relative modular entropy language.

The logarithmic relative-modular formula is not asserted here.  It must be
proved or imported from a dedicated owner module.
-/
structure RelativeModularEntropyCarrier
    (State Value ModularOperator : Type*) where
  relativeModularOperator : State → State → ModularOperator
  modularHamiltonian : ModularOperator → Value
  relativeEntropy : State → State → Value

namespace RelativeModularEntropyCarrier

variable {State Value ModularOperator : Type*}
variable (R : RelativeModularEntropyCarrier State Value ModularOperator)

@[rep_depth operator]
theorem relativeModularOperator_apply (ρ σ : State) :
    R.relativeModularOperator ρ σ = R.relativeModularOperator ρ σ := rfl

@[rep_depth operator]
theorem modularHamiltonian_apply (Δ : ModularOperator) :
    R.modularHamiltonian Δ = R.modularHamiltonian Δ := rfl

@[rep_depth operator]
theorem relativeEntropy_apply (ρ σ : State) :
    R.relativeEntropy ρ σ = R.relativeEntropy ρ σ := rfl

end RelativeModularEntropyCarrier

/--
Carrier for ergodic invariant readout language.

Mean-ergodic convergence and invariant-sector theorems are not fields here.
-/
structure ModularErgodicInvariantCarrier
    (Alg : Type*) where
  modularFlow : ℝ → Alg → Alg
  ergodicProjection : Alg → Alg

namespace ModularErgodicInvariantCarrier

variable {Alg : Type*}
variable (E : ModularErgodicInvariantCarrier Alg)

@[rep_depth operator]
theorem modularFlow_apply (t : ℝ) (A : Alg) :
    E.modularFlow t A = E.modularFlow t A := rfl

@[rep_depth operator]
theorem ergodicProjection_apply (A : Alg) :
    E.ergodicProjection A = E.ergodicProjection A := rfl

end ModularErgodicInvariantCarrier

/--
Carrier for classical chart readout from operator-information channels.

The chart theorem is not a field.  A downstream owner module must prove any
invariance, smoothness, or coordinate-chart property directly.
-/
structure ClassicalChartReadoutCarrier
    (Alg State Value Chart : Type*) where
  bridge : OperatorInformationGeometryCarrier Alg State Value
  chartReadout : Alg → Chart

namespace ClassicalChartReadoutCarrier

variable {Alg State Value Chart : Type*}
variable (C : ClassicalChartReadoutCarrier Alg State Value Chart)

@[rep_depth operator]
theorem chartReadout_apply (A : Alg) :
    C.chartReadout A = C.chartReadout A := rfl

end ClassicalChartReadoutCarrier

end InfoGeometry.Canonical.OperatorInformationGeometryBridge
