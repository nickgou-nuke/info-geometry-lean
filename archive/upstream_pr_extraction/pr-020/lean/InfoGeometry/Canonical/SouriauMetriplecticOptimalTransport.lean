import InfoGeometry.Canonical.MetricTransportWitness
import InfoGeometry.Canonical.SouriauMetriplecticContext
import InfoGeometry.Canonical.SouriauThermodynamics
import Mathlib

/-!
# InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport

State-dynamics layer for the Souriau/Metriplectic/Optimal-Transport corridor.

This module is intentionally conservative:

- Souriau thermodynamics supplies the Lie-geometric thermal readout
  `K_β(x) = ⟪J(x), β⟫`.
- Metriplectic data keeps the reversible Poisson sector separate from the
  dissipative metric sector.
- Optimal transport is carried by an explicit metric/cost/mobility witness.
- JKO updates are recorded as a variational witness, not a convergence theorem.
- Metric transport of projector layers is imported as a compatibility gate,
  not conflated with transport on probability densities.

No closure claim is made here.
-/

namespace InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport

open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Canonical.MetricTransportWitness
open InfoGeometry.Canonical.SouriauMetriplectic
open InfoGeometry.Canonical.SouriauThermodynamics

/-- Phantom-parameter generalized temperature carrier used by this conservative packet. -/
structure GeneralizedSouriauTemperature (LieAlgebra : Type*) where
  beta : LieAlgebra

abbrev Density (State : Type*) := State → ℝ

/-- Souriau Lie-thermodynamic data: moment map, generalized temperature, and pairing. -/
@[rep_depth thermo]
structure SouriauLieThermoData
    (State LieGroup LieAlgebra LieDual : Type*) where
  momentMap : State → LieDual
  beta : GeneralizedSouriauTemperature LieAlgebra
  pairing : LieDual → LieAlgebra → ℝ

namespace SouriauLieThermoData

variable {State LieGroup LieAlgebra LieDual : Type*}

/-- Souriau thermal Hamiltonian `K_β(x) = ⟪J(x), β⟫`. -/
@[rep_depth thermo]
def K_beta (D : SouriauLieThermoData State LieGroup LieAlgebra LieDual)
    (x : State) : ℝ :=
  D.pairing (D.momentMap x) D.beta.beta

/-- Formal Gibbs weight `exp(-K_β(x))`. -/
@[rep_depth thermo]
noncomputable def gibbsWeight
    (D : SouriauLieThermoData State LieGroup LieAlgebra LieDual)
    (x : State) : ℝ :=
  Real.exp (-D.K_beta x)

@[rep_depth thermo]
theorem K_beta_eq_pairing
    (D : SouriauLieThermoData State LieGroup LieAlgebra LieDual)
    (x : State) :
    D.K_beta x = D.pairing (D.momentMap x) D.beta.beta :=
  rfl

@[rep_depth thermo]
theorem gibbsWeight_eq_exp_neg_K_beta
    (D : SouriauLieThermoData State LieGroup LieAlgebra LieDual)
    (x : State) :
    D.gibbsWeight x = Real.exp (-D.K_beta x) :=
  rfl

end SouriauLieThermoData

/-- Reversible Souriau transport packet on density states. -/
@[rep_depth thermo]
structure SouriauTransportFlow (State LieGroup LieAlgebra LieDual : Type*) where
  thermo : SouriauLieThermoData State LieGroup LieAlgebra LieDual
  hamiltonianVectorField : State → State
  reversibleDensityTransport : Density State → Density State
  reversibleTransport_eq_hamiltonian : Prop
  preservesLiouvilleMeasure : Prop
  preservesGibbsWeight : Prop
  preservesEntropyFunctional : Prop

/-- Metriplectic bracket data: reversible Poisson sector plus dissipative metric sector. -/
@[rep_depth thermo]
structure MetriplecticData (Observable : Type*) where
  poissonBracket : Observable → Observable → ℝ
  metricBracket : Observable → Observable → ℝ
  energy : Observable
  entropy : Observable
  poisson_skew : Prop
  poisson_jacobi : Prop
  metric_symmetric : Prop
  metric_positive_semidefinite : Prop
  entropy_is_poisson_casimir : Prop
  energy_is_metric_casimir : Prop
  entropyProductionNonnegative : Prop

namespace MetriplecticData

variable {Observable : Type*}

/-- Formal total rate `Poisson + metric` for the selected observable. -/
@[rep_depth thermo]
def totalRate (D : MetriplecticData Observable) (F : Observable) : ℝ :=
  D.poissonBracket F D.energy + D.metricBracket F D.entropy

end MetriplecticData

/-- Explicit metriplectic consistency packet. -/
@[rep_depth thermo]
structure MetriplecticConsistencyWitness (Observable : Type*) where
  data : MetriplecticData Observable
  reversiblePreservesEnergy : Prop
  dissipativeProducesEntropy : Prop
  entropyProduction_nonneg : Prop

/-- Optimal-transport metric witness on density states. -/
@[rep_depth thermo]
structure OptimalTransportMetricWitness (State : Type*) where
  cost : State → State → ℝ
  mobilityOperator : Density State → Density State
  wassersteinMetric : Prop
  continuityEquation : Prop
  transportRegularity : Prop
  metricPositiveSemidefinite : Prop

/-- Free-energy functional with the entropy/expectation split recorded explicitly. -/
@[rep_depth thermo]
structure FreeEnergyFunctional (State : Type*) where
  freeEnergy : Density State → ℝ
  entropyTerm : Density State → ℝ
  expectationTerm : Density State → ℝ
  freeEnergy_eq :
    ∀ ρ, freeEnergy ρ = entropyTerm ρ + expectationTerm ρ
  convexityWitness : Prop
  coercivityWitness : Prop
  lowerSemicontinuityWitness : Prop

namespace FreeEnergyFunctional

variable {State : Type*}

@[rep_depth thermo]
theorem freeEnergy_eq_split
    (F : FreeEnergyFunctional State) (ρ : Density State) :
    F.freeEnergy ρ = F.entropyTerm ρ + F.expectationTerm ρ :=
  F.freeEnergy_eq ρ

end FreeEnergyFunctional

/-- Dissipative Wasserstein/Onsager gradient-flow witness. -/
@[rep_depth thermo]
structure WassersteinGradientFlow (State : Type*) where
  ot : OptimalTransportMetricWitness State
  freeEnergy : FreeEnergyFunctional State
  dissipativeFlow : Density State → Density State
  freeEnergyDecay : Prop
  jkoCompatible : Prop

/-- JKO step recorded as a variational witness. -/
@[rep_depth thermo]
structure JKOTimeStep (State : Type*) where
  previous : Density State
  next : Density State
  objective : Density State → ℝ
  stepSize : ℝ
  stepSize_nonneg : 0 ≤ stepSize
  minimizing : ∀ ρ, objective next ≤ objective ρ

/-- Stationary equilibrium candidate for the combined state-dynamics layer. -/
@[rep_depth thermo]
structure EquilibriumCandidate (State : Type*) where
  density : Density State
  reversibleStationary : Prop
  dissipativeStationary : Prop
  freeEnergyMinimizer : Prop

/--
State-dynamics packet combining Souriau transport, metriplectic split, and
optimal transport.

The object is intentionally a witness container, not a global theorem.
-/
@[rep_depth thermo]
structure SouriauMetriplecticOTFlow
    (State LieGroup LieAlgebra LieDual Observable : Type*) where
  souriau : SouriauLieThermoData State LieGroup LieAlgebra LieDual
  transport : SouriauTransportFlow State LieGroup LieAlgebra LieDual
  metriplectic : MetriplecticConsistencyWitness Observable
  ot : OptimalTransportMetricWitness State
  freeEnergy : FreeEnergyFunctional State
  reversibleFlow : Density State → Density State
  dissipativeFlow : Density State → Density State
  totalFlow : Density State → Density State
  reversible_part_eq_lieTransport : Prop
  dissipative_part_eq_gradientFlow : Prop
  totalFlow_eq_add : ∀ ρ, totalFlow ρ = reversibleFlow ρ + dissipativeFlow ρ
  entropyProduction_nonnegative : Prop

namespace SouriauMetriplecticOTFlow

variable {State LieGroup LieAlgebra LieDual Observable : Type*}

/-- The reversible and dissipative pieces add pointwise on densities. -/
@[rep_depth thermo]
theorem totalFlow_eq_add_at
    (F : SouriauMetriplecticOTFlow State LieGroup LieAlgebra LieDual Observable)
    (ρ : Density State) :
    F.totalFlow ρ = F.reversibleFlow ρ + F.dissipativeFlow ρ :=
  F.totalFlow_eq_add ρ

end SouriauMetriplecticOTFlow

/--
Compatibility gate connecting the projector-side metric transport witness and
the probability-density transport witness.
-/
@[rep_depth transport]
structure MetricTransportCompatibility
    {R : Type*} [Ring R]
    (P P' : ProjectorPair R)
    (State : Type*) where
  projectorTransport : MetricCompensatorWitness P P'
  otWitness : OptimalTransportMetricWitness State
  compatibility : Prop

/-- Commutative log Radon--Nikodym / relative modular Hamiltonian packet. -/
@[rep_depth thermo]
structure LogRadonNikodymHamiltonian (State : Type*) where
  rho : Density State
  sigma : Density State
  logRN : Density State
  relativeModularHamiltonian : Density State
  logRN_definition : Prop
  relativeModularHamiltonian_definition : Prop

/-- Relative entropy readout carried by the logarithmic modular packet. -/
@[rep_depth thermo]
structure RelativeEntropyReadout (State : Type*) where
  logData : LogRadonNikodymHamiltonian State
  relativeEntropy : ℝ
  expectationWitness : Prop
  relativeEntropy_eq_expectation : Prop

/-- Jacobian / metric-transport correction readout. -/
@[rep_depth thermo]
structure JacobianPotentialReadout (State : Type*) where
  jacobianFactor : ℝ
  modularCorrection : ℝ
  additiveCorrection : Prop

/-- Quantum modular Hamiltonian witness. -/
@[rep_depth thermo]
structure ModularHamiltonianQuantum (State : Type*) where
  densityMatrix : Type*
  modularHamiltonian : densityMatrix → densityMatrix
  partitionFunction : densityMatrix → ℝ
  normalizedState : densityMatrix → densityMatrix
  modularHamiltonian_definition : Prop
  normalizedState_definition : Prop

/-- Duhamel/Kubo operator-derivative witness. -/
@[rep_depth thermo]
structure DuhamelOperatorDerivativeWitness (State : Type*) where
  operatorFamily : State → Type*
  operatorDerivative : Prop
  duhamelFormula : Prop
  higherOrderedSimplexWitness : Prop

/-- Mellin/Rényi modular deformation packet. -/
@[rep_depth thermo]
structure RenyiModularDeformation (State : Type*) where
  alpha : ℝ
  renyiPartition : ℝ
  renyiEntropy : ℝ
  relativeRenyi : ℝ
  mellinWitness : Prop
  petzWitness : Prop
  sandwichedWitness : Prop

/-- Operatorial logarithmic potential readout layer. -/
@[rep_depth thermo]
structure OperatorialLogPotentialLayer (State : Type*) where
  logRN : LogRadonNikodymHamiltonian State
  relativeEntropy : RelativeEntropyReadout State
  jacobian : JacobianPotentialReadout State
  modularQuantum : ModularHamiltonianQuantum State
  duhamel : DuhamelOperatorDerivativeWitness State
  renyi : RenyiModularDeformation State
  thermodynamicForce : Prop
  force_as_relativeModularGradient : Prop

/--
Finite bridge packet: a finite Souriau/Onsager shadow equipped with an
optimal-transport metric witness and a metric-transport compatibility gate.
-/
@[rep_depth thermo]
structure FiniteSouriauMetriplecticOTBridge
    [Fintype α] [Nonempty α]
    {R : Type*} [Ring R]
    (P P' : ProjectorPair R) where
  metriplectic : MetriplecticContext (α := α)
  ot : OptimalTransportMetricWitness α
  compatibility : MetricTransportCompatibility P P' α
  finiteFreeEnergy : FreeEnergyFunctional α
  equilibrium : EquilibriumCandidate α

end InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
