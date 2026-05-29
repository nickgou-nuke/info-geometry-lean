import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Canonical.RelativeModularPotential
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.EinsteinAnomalyOperator

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ThermodynamicGenerator

Thin operatorial thermodynamic bridge on the doubled carrier.

This file does not introduce a new thermodynamic ontology. It only packages the
existing owner surface:

- the state-relative modular generator as the Souriau temperature vector,
- the operatorial Gibbs weight `exp(-β G)` on the same carrier,
- the first-variation current split into gauge and source branches,
- the comparison-state metric/phase readout pair,
- and the comparison-state channel-correlation pair carried by the induced
  relational datum.
-/

namespace InfoGeometry.Canonical.ThermodynamicGenerator

open InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Souriau temperature vector: the existing state-relative modular generator. -/
@[rep_depth transport]
noncomputable def souriauTemperatureVector
    (P : PotentialDatum (E := E)) (ψ : H₂) : EndH :=
  InfoGeometry.Canonical.RelativeModularPotential.transportGenerator (E := E) P ψ

@[rep_depth transport, simp] theorem souriauTemperatureVector_eq_generator
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    souriauTemperatureVector (E := E) P ψ = generator (E := E) P ψ := rfl

@[rep_depth transport, simp] theorem souriauTemperatureVector_eq_transportGenerator
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    souriauTemperatureVector (E := E) P ψ
      =
    InfoGeometry.Canonical.RelativeModularPotential.transportGenerator (E := E) P ψ := rfl

@[rep_depth transport, simp] theorem souriauTemperatureVector_eq_stateRelativeModularGenerator
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    souriauTemperatureVector (E := E) P ψ
      =
    stateRelativeModularGenerator (E := E) P.modularData ψ := by
  rfl

/-- Operatorial Gibbs weight `exp(-β G)` attached to the Souriau generator. -/
@[rep_depth transport]
noncomputable def operatorialGibbsWeight
    (P : PotentialDatum (E := E)) (ψ : H₂) (β : ℝ) : EndH :=
  NormedSpace.exp (-β • souriauTemperatureVector (E := E) P ψ)

@[rep_depth transport, simp] theorem operatorialGibbsWeight_zero
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    operatorialGibbsWeight (E := E) P ψ 0 = (1 : EndH) := by
  simp [operatorialGibbsWeight]

/--
Evaluating the operatorial Gibbs weight is exactly the partition function for
the negated Souriau generator.
-/
@[rep_depth transport, simp]
theorem apply_operatorialGibbsWeight_eq_informationPartitionFunction
    (ω : EndH →L[ℝ] ℝ)
    (P : PotentialDatum (E := E)) (ψ : H₂) (β : ℝ) :
    ω (operatorialGibbsWeight (E := E) P ψ β)
      =
    informationPartitionFunction ω (-souriauTemperatureVector (E := E) P ψ) β := by
  simp [operatorialGibbsWeight, informationPartitionFunction]

/--
The operatorial Gibbs expectation has infinitesimal value given by the negated
Souriau temperature vector.
-/
@[rep_depth transport, capstone]
theorem hasDerivAt_apply_operatorialGibbsWeight_zero
    (ω : EndH →L[ℝ] ℝ)
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    HasDerivAt
      (fun β : ℝ => ω (operatorialGibbsWeight (E := E) P ψ β))
      (ω (-souriauTemperatureVector (E := E) P ψ)) 0 := by
  simpa [apply_operatorialGibbsWeight_eq_informationPartitionFunction] using
    (hasDerivAt_informationPartitionFunction_zero
      (ω := ω) (K := -souriauTemperatureVector (E := E) P ψ))

@[rep_depth transport]
theorem deriv_apply_operatorialGibbsWeight_zero
    (ω : EndH →L[ℝ] ℝ)
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    deriv (fun β : ℝ => ω (operatorialGibbsWeight (E := E) P ψ β)) 0
      =
    ω (-souriauTemperatureVector (E := E) P ψ) :=
  (hasDerivAt_apply_operatorialGibbsWeight_zero
    (E := E) (ω := ω) (P := P) (ψ := ψ)).deriv

/-- First variation is the probe applied to the full induced modular dynamics. -/
@[rep_depth transport, simp]
theorem firstVariation_eq_probe_stateInducedDynamics
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    firstVariation (E := E) P ψ A
      =
    P.probe (stateInducedDynamics (E := E) P.modularData ψ A) := rfl

/-- Thermodynamic current splits into gauge-preserving and source branches. -/
@[rep_depth transport]
theorem firstVariation_eq_gaugeVariation_add_sourceVariation
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    firstVariation (E := E) P ψ A
      =
    gaugeVariation (E := E) P ψ A + sourceVariation (E := E) P ψ A :=
  RelativeModularPotential.firstVariation_eq_gauge_add_source
    (E := E) P ψ A

/--
The comparison-state second-variation readout packages directly into the
operatorial metric/phase pair of the induced dynamics.
-/
@[rep_depth transport, simp]
theorem comparisonReadout_pair_apply
    (P : PotentialDatum (E := E))
    (comparison : H₂) (A : EndH) (u v : H₂) :
    ( comparisonMetricReadout (E := E) P comparison A u v
    , comparisonPhaseReadout (E := E) P comparison A u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (stateInducedDynamics (E := E) P.modularData comparison A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (stateInducedDynamics (E := E) P.modularData comparison A) u v ) := by
  rfl

/--
The induced relational datum recovers the comparison-state channel metric/phase
pair on perturbation channels.
-/
@[rep_depth transport, simp]
theorem toRelationalInformationDatum_comparisonMetricPhase_pair_apply
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    ( comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
    , comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y )
      =
    ( comparisonStateGeneratorMetric (E := E) comparison X Y
    , comparisonStateGeneratorPhase (E := E) comparison X Y ) := by
  apply Prod.ext
  · simp [RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorMetric_apply]
  · simp

/-- Faithfulness of the thermodynamic probe on doubled-space operators. -/
@[rep_depth transport]
def ProbeFaithful
    (P : PotentialDatum (E := E)) : Prop :=
  ∀ A : EndH, P.probe A = 0 → A = 0

/--
Operatorial Killing predicate for the entropy potential:
the induced thermodynamic dynamics vanishes at the chosen state.
-/
@[rep_depth transport]
def IsPotentialKillingOperator
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) : Prop :=
  stateInducedDynamics (E := E) P.modularData ψ A = 0

/-- Operatorial Killing implies vanishing first variation of the potential. -/
@[rep_depth transport]
theorem firstVariation_eq_zero_of_isPotentialKillingOperator
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hKill : IsPotentialKillingOperator (E := E) P ψ A) :
    firstVariation (E := E) P ψ A = 0 := by
  unfold IsPotentialKillingOperator at hKill
  rw [firstVariation_eq_probe_stateInducedDynamics, hKill]
  simp

/--
Under a faithful probe, vanishing first variation is equivalent to the
operatorial Killing condition.
-/
@[rep_depth transport]
theorem isPotentialKillingOperator_iff_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P) :
    IsPotentialKillingOperator (E := E) P ψ A
      ↔
    firstVariation (E := E) P ψ A = 0 := by
  constructor
  · exact firstVariation_eq_zero_of_isPotentialKillingOperator (E := E) P ψ A
  · intro hFirst
    refine hFaithful (stateInducedDynamics (E := E) P.modularData ψ A) ?_
    simpa [firstVariation_eq_probe_stateInducedDynamics] using hFirst

/--
Faithful thermodynamic probing upgrades vanishing first variation into the
operatorial Killing condition.
-/
@[rep_depth transport]
theorem isPotentialKillingOperator_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    IsPotentialKillingOperator (E := E) P ψ A :=
  (isPotentialKillingOperator_iff_firstVariation_eq_zero_of_probeFaithful
    (E := E) P ψ A hFaithful).2 hFirst

/--
At the same state, an operatorial Killing channel has vanishing bundled
operatorial metric/phase thermodynamic readout.
-/
  @[rep_depth transport]
theorem stateQGTReadout_pair_eq_zero_of_isPotentialKillingOperator
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hKill : IsPotentialKillingOperator (E := E) P ψ A) :
    ( ((StateDependentTransport.stateQGTReadout (E := E) P.modularData ψ A).metric)
    , ((StateDependentTransport.stateQGTReadout (E := E) P.modularData ψ A).phase) )
      =
    (0, 0) := by
  exact stateQGTReadout_pair_eq_zero_of_stateInducedDynamics_eq_zero
    (E := E) (M := P.modularData) (ψ := ψ) (A := A) hKill

/--
At the same state, an operatorial Killing channel has vanishing thermodynamic
metric and phase readouts.
-/
@[rep_depth transport]
theorem comparisonReadout_pair_eq_zero_of_isPotentialKillingOperator
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hKill : IsPotentialKillingOperator (E := E) P ψ A) :
    (comparisonMetricReadout (E := E) P ψ A,
      comparisonPhaseReadout (E := E) P ψ A)
      =
    (0, 0) := by
  simpa [RelativeModularPotential.comparisonMetricReadout,
    RelativeModularPotential.comparisonPhaseReadout] using
    stateQGTReadout_pair_eq_zero_of_isPotentialKillingOperator
      (E := E) (P := P) (ψ := ψ) (A := A) hKill

/--
Faithful thermodynamic probing upgrades vanishing first variation directly into
vanishing state-QGT readout on the doubled carrier.
-/
@[rep_depth transport]
theorem stateQGTReadout_pair_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    ( ((StateDependentTransport.stateQGTReadout (E := E) P.modularData ψ A).metric)
    , ((StateDependentTransport.stateQGTReadout (E := E) P.modularData ψ A).phase) )
      =
    (0, 0) := by
  exact stateQGTReadout_pair_eq_zero_of_isPotentialKillingOperator
    (E := E) (P := P) (ψ := ψ) (A := A)
    (isPotentialKillingOperator_of_firstVariation_eq_zero_of_probeFaithful
      (E := E) P ψ A hFaithful hFirst)

/--
Vanishing comparison-state metric readout is faithful: it forces the underlying
induced thermodynamic dynamics to vanish.
-/
@[rep_depth transport]
theorem stateInducedDynamics_eq_zero_of_comparisonMetricReadout_eq_zero
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hMetric : comparisonMetricReadout (E := E) P ψ A = 0) :
    stateInducedDynamics (E := E) P.modularData ψ A = 0 := by
  ext u
  · apply ext_inner_right ℝ
    intro v
    have hEval :=
      congrArg
        (fun B : LinearMap.BilinForm ℝ H₂ =>
          B u (to_doubled v (0 : E)))
        hMetric
    simpa [RelativeModularPotential.comparisonMetricReadout_apply,
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_apply,
      to_doubled] using hEval
  · apply ext_inner_right ℝ
    intro v
    have hEval :=
      congrArg
        (fun B : LinearMap.BilinForm ℝ H₂ =>
          B u (to_doubled (0 : E) v))
        hMetric
    simpa [RelativeModularPotential.comparisonMetricReadout_apply,
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_apply,
      to_doubled] using hEval

/--
Owner-dynamics stationarity forces the comparison metric readout to vanish,
without requiring callers to supply a separate metric-stationarity packet.
-/
@[rep_depth transport]
theorem comparisonMetricReadout_eq_zero_of_stateInducedDynamics_eq_zero
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hDyn : stateInducedDynamics (E := E) P.modularData ψ A = 0) :
    comparisonMetricReadout (E := E) P ψ A = 0 := by
  have hPair :=
    comparisonReadout_pair_eq_zero_of_isPotentialKillingOperator
      (E := E) P ψ A hDyn
  simpa using congrArg Prod.fst hPair

/--
Owner-dynamics stationarity forces the comparison phase readout to vanish,
without requiring callers to supply a separate phase-stationarity packet.
-/
@[rep_depth transport]
theorem comparisonPhaseReadout_eq_zero_of_stateInducedDynamics_eq_zero
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hDyn : stateInducedDynamics (E := E) P.modularData ψ A = 0) :
    comparisonPhaseReadout (E := E) P ψ A = 0 := by
  have hPair :=
    comparisonReadout_pair_eq_zero_of_isPotentialKillingOperator
      (E := E) P ψ A hDyn
  simpa using congrArg Prod.snd hPair

/--
The comparison-metric stationarity packet is equivalent to the underlying
owner dynamics vanishing.  Downstream routes can now consume the owner dynamics
witness directly instead of carrying the explicit metric-readout hypothesis.
-/
@[rep_depth transport]
theorem comparisonMetricReadout_eq_zero_iff_stateInducedDynamics_eq_zero
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    comparisonMetricReadout (E := E) P ψ A = 0
      ↔
    stateInducedDynamics (E := E) P.modularData ψ A = 0 := by
  constructor
  · exact stateInducedDynamics_eq_zero_of_comparisonMetricReadout_eq_zero
      (E := E) P ψ A
  · exact comparisonMetricReadout_eq_zero_of_stateInducedDynamics_eq_zero
      (E := E) P ψ A

/--
Metric stationarity of the comparison-state thermodynamic readout is equivalent
to the operatorial Killing condition on the entropy potential.
-/
@[rep_depth transport]
theorem isPotentialKillingOperator_iff_comparisonMetricReadout_eq_zero
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    IsPotentialKillingOperator (E := E) P ψ A
      ↔
    comparisonMetricReadout (E := E) P ψ A = 0 := by
  constructor
  · intro hKill
    have hPair :=
      comparisonReadout_pair_eq_zero_of_isPotentialKillingOperator
        (E := E) P ψ A hKill
    simpa using congrArg Prod.fst hPair
  · intro hMetric
    exact stateInducedDynamics_eq_zero_of_comparisonMetricReadout_eq_zero
      (E := E) P ψ A hMetric

/--
Thermodynamic equilibrium at a comparison state: both Bogoliubov metric and
phase readouts vanish on the induced channel.
-/
@[rep_depth transport]
def IsThermodynamicReadoutStationary
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) : Prop :=
  (comparisonMetricReadout (E := E) P ψ A,
    comparisonPhaseReadout (E := E) P ψ A) = (0, 0)

/--
Souriau equilibrium on the entropy-potential surface is exactly vanishing
Bogoliubov metric/phase thermodynamic readout at the comparison state.
-/
@[rep_depth transport]
theorem isPotentialKillingOperator_iff_isThermodynamicReadoutStationary
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    IsPotentialKillingOperator (E := E) P ψ A
      ↔
    IsThermodynamicReadoutStationary (E := E) P ψ A := by
  constructor
  · intro hKill
    exact comparisonReadout_pair_eq_zero_of_isPotentialKillingOperator
      (E := E) P ψ A hKill
  · intro hReadout
    have hMetric : comparisonMetricReadout (E := E) P ψ A = 0 := by
      simpa [IsThermodynamicReadoutStationary] using congrArg Prod.fst hReadout
    exact
      (isPotentialKillingOperator_iff_comparisonMetricReadout_eq_zero
        (E := E) P ψ A).2 hMetric

/--
Under a faithful probe, thermodynamic readout stationarity is equivalent to
vanishing first variation of the entropy potential.
-/
@[rep_depth transport]
theorem isThermodynamicReadoutStationary_iff_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P) :
    IsThermodynamicReadoutStationary (E := E) P ψ A
      ↔
    firstVariation (E := E) P ψ A = 0 := by
  calc
    IsThermodynamicReadoutStationary (E := E) P ψ A
        ↔ IsPotentialKillingOperator (E := E) P ψ A := by
          rw [isPotentialKillingOperator_iff_isThermodynamicReadoutStationary]
    _ ↔ firstVariation (E := E) P ψ A = 0 :=
      isPotentialKillingOperator_iff_firstVariation_eq_zero_of_probeFaithful
        (E := E) P ψ A hFaithful

/--
Faithful thermodynamic probing upgrades vanishing first variation into the
bundled thermodynamic readout-stationarity predicate.
-/
@[rep_depth transport]
theorem isThermodynamicReadoutStationary_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    IsThermodynamicReadoutStationary (E := E) P ψ A :=
  (isThermodynamicReadoutStationary_iff_firstVariation_eq_zero_of_probeFaithful
    (E := E) P ψ A hFaithful).2 hFirst

/--
Faithful thermodynamic probing upgrades vanishing first variation into vanishing
comparison-state metric/phase readout directly.
-/
@[rep_depth transport]
theorem comparisonReadout_pair_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    (comparisonMetricReadout (E := E) P ψ A,
      comparisonPhaseReadout (E := E) P ψ A) = (0, 0) :=
  isThermodynamicReadoutStationary_of_firstVariation_eq_zero_of_probeFaithful
    (E := E) P ψ A hFaithful hFirst

/--
Faithful thermodynamic probing upgrades vanishing first variation into vanishing
comparison-state metric readout directly.
-/
@[rep_depth transport]
theorem comparisonMetricReadout_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    comparisonMetricReadout (E := E) P ψ A = 0 := by
  exact congrArg Prod.fst
    (comparisonReadout_pair_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
      (E := E) P ψ A hFaithful hFirst)

/--
Faithful thermodynamic probing upgrades vanishing first variation all the way to
zero induced thermodynamic dynamics, removing the intermediate explicit
comparison-metric vanishing packet from downstream routes.
-/
@[rep_depth transport]
theorem stateInducedDynamics_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    stateInducedDynamics (E := E) P.modularData ψ A = 0 := by
  exact stateInducedDynamics_eq_zero_of_comparisonMetricReadout_eq_zero
    (E := E) P ψ A
    (comparisonMetricReadout_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
      (E := E) P ψ A hFaithful hFirst)

/--
Faithful thermodynamic probing upgrades vanishing first variation into vanishing
comparison-state phase readout directly.
-/
@[rep_depth transport]
theorem comparisonPhaseReadout_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    comparisonPhaseReadout (E := E) P ψ A = 0 := by
  exact congrArg Prod.snd
    (comparisonReadout_pair_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
      (E := E) P ψ A hFaithful hFirst)

end Core

section GrandCanonical

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Grand-canonical deformation of a doubled-space operator seed. -/
@[rep_depth krein]
noncomputable def operatorialGrandCanonicalGenerator
    (B : HyperbolicMixingParams) (H : EndH) (μ : ℝ) : EndH :=
  grandCanonicalFockGenerator (E := E) B H μ

/-- Unnormalized grand-canonical operator weight on the doubled carrier. -/
@[rep_depth krein]
noncomputable def operatorialGrandCanonicalWeight
    (B : HyperbolicMixingParams) (H : EndH) (μ τ : ℝ) : EndH :=
  NormedSpace.exp (τ • operatorialGrandCanonicalGenerator (E := E) B H μ)

/-- Massieu/log-partition potential of the operatorial grand-canonical ensemble. -/
@[rep_depth krein]
noncomputable def operatorialGrandCanonicalMassieuPotential
    (ω : EndH →L[ℝ] ℝ)
    (B : HyperbolicMixingParams) (H : EndH) (μ : ℝ) : ℝ → ℝ :=
  operatorMassieuPotential (E := E) ω
    (operatorialGrandCanonicalGenerator (E := E) B H μ)

/-- Primitive infinitesimal expectation of the operatorial grand-canonical generator. -/
@[rep_depth krein]
noncomputable def operatorialGrandCanonicalMassieuExpectation
    (ω : EndH →L[ℝ] ℝ)
    (B : HyperbolicMixingParams) (H : EndH) (μ : ℝ) : ℝ :=
  operatorMassieuExpectation ω
    (operatorialGrandCanonicalGenerator (E := E) B H μ)

@[rep_depth krein, simp]
theorem apply_operatorialGrandCanonicalWeight_eq_informationPartitionFunction
    (ω : EndH →L[ℝ] ℝ)
    (B : HyperbolicMixingParams) (H : EndH) (μ τ : ℝ) :
    ω (operatorialGrandCanonicalWeight (E := E) B H μ τ)
      =
    informationPartitionFunction ω
      (operatorialGrandCanonicalGenerator (E := E) B H μ) τ := by
  rfl

@[rep_depth krein]
theorem operatorialGrandCanonicalGenerator_eq_observable_of_zeroChemicalPotential
    (B : HyperbolicMixingParams) (H : EndH) :
    operatorialGrandCanonicalGenerator (E := E) B H 0 = H := by
  change H - 0 • bogoliubovNumberOperator (E := E) B = H
  simp

@[rep_depth krein]
theorem operatorialGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw
    (ω : EndH →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH) = 1)
    (B : HyperbolicMixingParams) (H : EndH) (μ : ℝ) :
    HasDerivAt
      (operatorialGrandCanonicalMassieuPotential (E := E) ω B H μ)
      (operatorialGrandCanonicalMassieuExpectation ω B H μ) 0 := by
  simpa [operatorialGrandCanonicalMassieuPotential,
    operatorialGrandCanonicalMassieuExpectation] using
    operatorMassieuPotential_normalizedInfinitesimalLaw
      (E := E) (ω := ω)
      (A := operatorialGrandCanonicalGenerator (E := E) B H μ) hω1

/-- Grand-canonical thermodynamic deformation of the state-relative modular generator. -/
@[rep_depth transport]
noncomputable def stateRelativeGrandCanonicalGenerator
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams) (μ : ℝ) : EndH :=
  operatorialGrandCanonicalGenerator (E := E) B
    (generator (E := E) P ψ) μ

/-- Grand-canonical Massieu potential of the state-relative modular generator. -/
@[rep_depth transport]
noncomputable def stateRelativeGrandCanonicalMassieuPotential
    (ω : EndH →L[ℝ] ℝ)
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams) (μ : ℝ) : ℝ → ℝ :=
  operatorialGrandCanonicalMassieuPotential (E := E) ω B
    (generator (E := E) P ψ) μ

/-- Primitive grand-canonical expectation of the state-relative modular generator. -/
@[rep_depth transport]
noncomputable def stateRelativeGrandCanonicalMassieuExpectation
    (ω : EndH →L[ℝ] ℝ)
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams) (μ : ℝ) : ℝ :=
  operatorialGrandCanonicalMassieuExpectation ω B
    (generator (E := E) P ψ) μ

@[rep_depth transport]
theorem stateRelativeGrandCanonicalGenerator_eq_generator_of_zeroChemicalPotential
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams) :
    stateRelativeGrandCanonicalGenerator (E := E) P ψ B 0 = generator (E := E) P ψ := by
  simpa [stateRelativeGrandCanonicalGenerator] using
    operatorialGrandCanonicalGenerator_eq_observable_of_zeroChemicalPotential
      (E := E) (B := B) (H := generator (E := E) P ψ)

@[rep_depth transport]
theorem stateRelativeGrandCanonicalMassieuExpectation_eq_value_of_zeroChemicalPotential
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams) :
    stateRelativeGrandCanonicalMassieuExpectation (E := E) P.probe P ψ B 0
      =
    value (E := E) P ψ := by
  change
      P.probe (operatorialGrandCanonicalGenerator (E := E) B (generator (E := E) P ψ) 0)
        =
      P.probe (generator (E := E) P ψ)
  simpa [operatorialGrandCanonicalGenerator] using
    congrArg P.probe
      (operatorialGrandCanonicalGenerator_eq_observable_of_zeroChemicalPotential
        (E := E) (B := B) (H := generator (E := E) P ψ))

@[rep_depth transport]
theorem stateRelativeGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw_of_zeroChemicalPotential
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams)
    (hProbe1 : P.probe (1 : EndH) = 1) :
    HasDerivAt
      (stateRelativeGrandCanonicalMassieuPotential (E := E) P.probe P ψ B 0)
      (value (E := E) P ψ) 0 := by
  have h :=
    operatorialGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw
      (E := E) (ω := P.probe) (hω1 := hProbe1)
      (B := B) (H := generator (E := E) P ψ) (μ := 0)
  convert h using 1
  · exact (stateRelativeGrandCanonicalMassieuExpectation_eq_value_of_zeroChemicalPotential
      (E := E) (P := P) (ψ := ψ) (B := B)).symm

@[rep_depth transport]
theorem stateRelativeGrandCanonicalGenerator_eq_generator_of_vacuumTransported
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E) (scalar Λ : ℝ)
    (V : SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection (E := E) K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    stateRelativeGrandCanonicalGenerator (E := E) P ψ B
        (einsteinInducedChemicalPotential R K x scalar Λ V Γ)
      =
    generator (E := E) P ψ := by
  simpa [stateRelativeGrandCanonicalGenerator, operatorialGrandCanonicalGenerator] using
    grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
      (E := E) (B := B) (H := generator (E := E) P ψ)
      (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hVacSplit

@[rep_depth transport]
theorem stateRelativeGrandCanonicalMassieuExpectation_eq_value_of_vacuumTransported
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E) (scalar Λ : ℝ)
    (V : SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection (E := E) K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    stateRelativeGrandCanonicalMassieuExpectation (E := E) P.probe P ψ B
        (einsteinInducedChemicalPotential R K x scalar Λ V Γ)
      =
    value (E := E) P ψ := by
  change
      P.probe
        (operatorialGrandCanonicalGenerator (E := E) B (generator (E := E) P ψ)
          (einsteinInducedChemicalPotential R K x scalar Λ V Γ))
        =
      P.probe (generator (E := E) P ψ)
  simpa [operatorialGrandCanonicalGenerator] using
    congrArg P.probe
      (grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
        (E := E) (B := B) (H := generator (E := E) P ψ)
        (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hVacSplit)

@[rep_depth transport]
theorem stateRelativeGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw_of_vacuumTransported
    (P : PotentialDatum (E := E)) (ψ : H₂)
    (B : HyperbolicMixingParams)
    (hProbe1 : P.probe (1 : EndH) = 1)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E) (scalar Λ : ℝ)
    (V : SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection (E := E) K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    HasDerivAt
      (stateRelativeGrandCanonicalMassieuPotential (E := E) P.probe P ψ B
        (einsteinInducedChemicalPotential R K x scalar Λ V Γ))
      (value (E := E) P ψ) 0 := by
  have h :=
    operatorialGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw
      (E := E) (ω := P.probe) (hω1 := hProbe1)
      (B := B) (H := generator (E := E) P ψ)
      (μ := einsteinInducedChemicalPotential R K x scalar Λ V Γ)
  convert h using 1
  · exact (stateRelativeGrandCanonicalMassieuExpectation_eq_value_of_vacuumTransported
      (E := E) (P := P) (ψ := ψ) (B := B) (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hVacSplit).symm

end GrandCanonical

section Anomaly

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Massieu potential of the lifted chiral anomaly operator. -/
@[rep_depth krein]
noncomputable def liftedChiralAnomalyMassieuPotential
    (CCI : CertifiedConformalInference E) (ω : EndH →L[ℝ] ℝ) : ℝ → ℝ :=
  operatorMassieuPotential (E := E) ω CCI.liftedChiralAnomalyOperator

/-- Primitive infinitesimal expectation of the lifted chiral anomaly operator. -/
@[rep_depth krein]
noncomputable def liftedChiralAnomalyMassieuExpectation
    (CCI : CertifiedConformalInference E) (ω : EndH →L[ℝ] ℝ) : ℝ :=
  operatorMassieuExpectation ω CCI.liftedChiralAnomalyOperator

/-- Massieu potential of the lifted projector-obstruction operator. -/
@[rep_depth krein]
noncomputable def liftedProjectorObstructionMassieuPotential
    (CCI : CertifiedConformalInference E) (ω : EndH →L[ℝ] ℝ) : ℝ → ℝ :=
  operatorMassieuPotential (E := E) ω CCI.liftedProjectorObstructionOperator

/-- Primitive infinitesimal expectation of the lifted projector-obstruction operator. -/
@[rep_depth krein]
noncomputable def liftedProjectorObstructionMassieuExpectation
    (CCI : CertifiedConformalInference E) (ω : EndH →L[ℝ] ℝ) : ℝ :=
  operatorMassieuExpectation ω CCI.liftedProjectorObstructionOperator

/-- Massieu potential of the lifted Einstein anomaly operator. -/
@[rep_depth krein]
noncomputable def liftedEinsteinAnomalyMassieuPotential
    (CCI : CertifiedConformalInference E) (ω : EndH →L[ℝ] ℝ) : ℝ → ℝ :=
  operatorMassieuPotential (E := E) ω CCI.liftedEinsteinAnomalyOperator

/-- Primitive infinitesimal expectation of the lifted Einstein anomaly operator. -/
@[rep_depth krein]
noncomputable def liftedEinsteinAnomalyMassieuExpectation
    (CCI : CertifiedConformalInference E) (ω : EndH →L[ℝ] ℝ) : ℝ :=
  operatorMassieuExpectation ω CCI.liftedEinsteinAnomalyOperator

@[rep_depth krein]
theorem liftedChiralAnomalyMassieuPotential_normalizedInfinitesimalLaw
    (CCI : CertifiedConformalInference E)
    (ω : EndH →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH) = 1) :
    HasDerivAt
      (liftedChiralAnomalyMassieuPotential (E := E) CCI ω)
      (liftedChiralAnomalyMassieuExpectation CCI ω) 0 := by
  simpa [liftedChiralAnomalyMassieuPotential,
    liftedChiralAnomalyMassieuExpectation] using
    operatorMassieuPotential_normalizedInfinitesimalLaw
      (E := E) (ω := ω) (A := CCI.liftedChiralAnomalyOperator) hω1

@[rep_depth krein]
theorem liftedProjectorObstructionMassieuPotential_normalizedInfinitesimalLaw
    (CCI : CertifiedConformalInference E)
    (ω : EndH →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH) = 1) :
    HasDerivAt
      (liftedProjectorObstructionMassieuPotential (E := E) CCI ω)
      (liftedProjectorObstructionMassieuExpectation CCI ω) 0 := by
  simpa [liftedProjectorObstructionMassieuPotential,
    liftedProjectorObstructionMassieuExpectation] using
    operatorMassieuPotential_normalizedInfinitesimalLaw
      (E := E) (ω := ω) (A := CCI.liftedProjectorObstructionOperator) hω1

@[rep_depth krein]
theorem liftedEinsteinAnomalyMassieuPotential_normalizedInfinitesimalLaw
    (CCI : CertifiedConformalInference E)
    (ω : EndH →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH) = 1) :
    HasDerivAt
      (liftedEinsteinAnomalyMassieuPotential (E := E) CCI ω)
      (liftedEinsteinAnomalyMassieuExpectation CCI ω) 0 := by
  simpa [liftedEinsteinAnomalyMassieuPotential,
    liftedEinsteinAnomalyMassieuExpectation] using
    operatorMassieuPotential_normalizedInfinitesimalLaw
      (E := E) (ω := ω) (A := CCI.liftedEinsteinAnomalyOperator) hω1

@[rep_depth krein]
theorem liftedEinsteinAnomalyMassieuExpectation_eq_neg_liftedProjectorObstructionMassieuExpectation_of_projectorAgreement
    (CCI : CertifiedConformalInference E)
    (ω : EndH →L[ℝ] ℝ)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector CCI.A CCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector CCI.A CCI.A_MP) :
    liftedEinsteinAnomalyMassieuExpectation (E := E) CCI ω
      =
    -liftedProjectorObstructionMassieuExpectation (E := E) CCI ω := by
  unfold liftedEinsteinAnomalyMassieuExpectation liftedProjectorObstructionMassieuExpectation
  rw [CCI.liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement
    hProj]
  simp [operatorMassieuExpectation]

@[rep_depth krein]
theorem liftedEinsteinAnomalyMassieuPotential_normalizedInfinitesimalLaw_of_projectorAgreement
    (CCI : CertifiedConformalInference E)
    (ω : EndH →L[ℝ] ℝ)
    (hω1 : ω (1 : EndH) = 1)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector CCI.A CCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector CCI.A CCI.A_MP) :
    HasDerivAt
      (liftedEinsteinAnomalyMassieuPotential (E := E) CCI ω)
      (-liftedProjectorObstructionMassieuExpectation (E := E) CCI ω) 0 := by
  have hDeriv :=
    liftedEinsteinAnomalyMassieuPotential_normalizedInfinitesimalLaw
      (E := E) (CCI := CCI) (ω := ω) hω1
  have hExp :
      liftedEinsteinAnomalyMassieuExpectation (E := E) CCI ω
        =
      -liftedProjectorObstructionMassieuExpectation (E := E) CCI ω :=
    liftedEinsteinAnomalyMassieuExpectation_eq_neg_liftedProjectorObstructionMassieuExpectation_of_projectorAgreement
      (E := E) (CCI := CCI) (ω := ω) hProj
  simpa [hExp] using hDeriv

end Anomaly

end InfoGeometry.Canonical.ThermodynamicGenerator
