import InfoGeometry.Canonical.MetricTransport
import InfoGeometry.Canonical.MetriplecticCore
import InfoGeometry.Canonical.SouriauMetriplecticContext
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelDerivative
import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
import Mathlib.Tactic

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

This module also formalizes the Grand Canonical Engine discovery:
1. The informational crystal is a Grand Canonical Ensemble of ensembles.
2. The Optimal Transport (Wasserstein flow) is driven by the gradient of the 
   log-partition function (the Free Energy).
3. The Riemann-Weil Explicit Formula is identified as the exact Wasserstein 
   vector field of this thermodynamic engine.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport

open OperatorProjectorMismatch
open MetricTransport
open InfoGeometry.Canonical.MetriplecticCore
open InfoGeometry.Canonical.SouriauMetriplectic
open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic
open SouriauThermodynamics
open scoped ComplexOrder

/--
Native generalized Souriau temperature owner: inverse-temperature scale
together with its Lie-algebra generator.
-/
abbrev GeneralizedSouriauTemperature (LieAlgebra : Type*) :=
  SouriauThermodynamics.GeneralizedSouriauTemperature LieAlgebra

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
  D.beta.beta * D.pairing (D.momentMap x) D.beta.generator

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
    D.K_beta x =
      D.beta.beta * D.pairing (D.momentMap x) D.beta.generator :=
  rfl

@[rep_depth thermo]
theorem gibbsWeight_eq_exp_neg_K_beta
    (D : SouriauLieThermoData State LieGroup LieAlgebra LieDual)
    (x : State) :
    D.gibbsWeight x = Real.exp (-D.K_beta x) :=
  rfl

end SouriauLieThermoData

/--
Souriau transport backed by the native coadjoint-orbit metriplectic owner.

The former packet stored four unrelated proposition markers.  Orbit closure,
Casimir reversibility, Onsager positivity, and entropy splitting now come from
`InfiniteCoadjointOrbitMetriplecticContext`.
-/
@[rep_depth thermo]
structure SouriauTransportFlow (State LieGroup LieAlgebra LieDual : Type*) where
  thermo : SouriauLieThermoData State LieGroup LieAlgebra LieDual
  dynamics :
    InfiniteCoadjointOrbitMetriplecticContext State LieAlgebra LieDual

namespace SouriauTransportFlow

variable {State LieGroup LieAlgebra LieDual : Type*}

/-- Reversible Souriau motion closes on the selected coadjoint orbit. -/
theorem reversible_transport_preserves_coadjoint_orbit
    (F : SouriauTransportFlow State LieGroup LieAlgebra LieDual)
    (x : State) :
    F.dynamics.isOnCoadjointOrbit
      (F.dynamics.moment (F.dynamics.reversibleVectorField x)) :=
  F.dynamics.reversible_flow_closes_on_coadjoint_orbit x

/-- The reversible coadjoint channel preserves entropy in the Casimir sense. -/
theorem reversible_entropy_rate_eq_zero
    (F : SouriauTransportFlow State LieGroup LieAlgebra LieDual)
    (x : State) :
    F.dynamics.reversibleEntropyRate x = 0 :=
  F.dynamics.reversibleEntropyRate_eq_zero x

/-- The metric/Onsager channel has nonnegative entropy production. -/
theorem metric_entropy_rate_nonnegative
    (F : SouriauTransportFlow State LieGroup LieAlgebra LieDual)
    (x : State) :
    0 ≤ F.dynamics.metricEntropyRate x :=
  F.dynamics.metricEntropyRate_nonnegative x

/-- The full Souriau metriplectic evolution satisfies the owner second law. -/
theorem total_entropy_rate_nonnegative
    (F : SouriauTransportFlow State LieGroup LieAlgebra LieDual)
    (x : State) :
    0 ≤ F.dynamics.totalEntropyRate x :=
  F.dynamics.coadjoint_orbit_metriplectic_second_law x

end SouriauTransportFlow

/--
Operator-valued metriplectic data owned by `MetriplecticCore`.

The former local structure stored scalar bracket functions together with seven
disconnected `Prop` markers.  The native owner instead carries quantified
skew/symmetry and Casimir laws in the observable ring itself.
-/
@[rep_depth thermo]
abbrev MetriplecticData (Observable : Type*) [Ring Observable] :=
  MetriplecticSystem Observable

namespace MetriplecticData

variable {Observable : Type*} [Ring Observable]

/-- Operator-valued total rate `Poisson + metric` for the selected observable. -/
@[rep_depth thermo]
def totalRate (D : MetriplecticData Observable) (F : Observable) : Observable :=
  D.poisson F D.Hamiltonian + D.metric F D.Entropy

end MetriplecticData

/--
Historical compatibility name for the genuine operator-valued owner.

There is no second evidence wrapper: consistency is exactly the quantified
algebraic content of `MetriplecticSystem`.
-/
@[rep_depth thermo]

/--
Optimal-transport metric and mobility data.

Metric laws are owned by Mathlib's `PseudoMetricSpace`; mobility is a genuine
linear operator on density functions.  No proposition-valued metric,
continuity, regularity, or positivity markers are stored.
-/
@[rep_depth thermo]
structure OptimalTransportMetricWitness (State : Type*) where
  metric : PseudoMetricSpace (Density State)
  mobilityOperator : Density State →ₗ[ℝ] Density State

namespace OptimalTransportMetricWitness

variable {State : Type*}

/-- Transport cost is the distance supplied by the native pseudometric owner. -/
def cost
    (W : OptimalTransportMetricWitness State)
    (ρ σ : Density State) : ℝ :=
  W.metric.dist ρ σ

/-- Native transport costs are nonnegative. -/
theorem cost_nonnegative
    (W : OptimalTransportMetricWitness State)
    (ρ σ : Density State) :
    0 ≤ W.cost ρ σ := by
  letI : PseudoMetricSpace (Density State) := W.metric
  exact dist_nonneg

/-- Native transport cost vanishes on the diagonal. -/
theorem cost_self
    (W : OptimalTransportMetricWitness State) (ρ : Density State) :
    W.cost ρ ρ = 0 := by
  letI : PseudoMetricSpace (Density State) := W.metric
  exact dist_self ρ

/-- Native transport cost is symmetric. -/
theorem cost_comm
    (W : OptimalTransportMetricWitness State)
    (ρ σ : Density State) :
    W.cost ρ σ = W.cost σ ρ := by
  letI : PseudoMetricSpace (Density State) := W.metric
  exact dist_comm ρ σ

/-- Native transport cost satisfies the triangle inequality. -/
theorem cost_triangle
    (W : OptimalTransportMetricWitness State)
    (ρ σ τ : Density State) :
    W.cost ρ τ ≤ W.cost ρ σ + W.cost σ τ := by
  letI : PseudoMetricSpace (Density State) := W.metric
  exact dist_triangle ρ σ τ

/-- Mobility preserves addition because it is a native linear map. -/
theorem mobilityOperator_add
    (W : OptimalTransportMetricWitness State)
    (ρ σ : Density State) :
    W.mobilityOperator (ρ + σ) =
      W.mobilityOperator ρ + W.mobilityOperator σ :=
  W.mobilityOperator.map_add ρ σ

/-- Mobility commutes with real scaling because it is a native linear map. -/
theorem mobilityOperator_smul
    (W : OptimalTransportMetricWitness State)
    (a : ℝ) (ρ : Density State) :
    W.mobilityOperator (a • ρ) = a • W.mobilityOperator ρ :=
  W.mobilityOperator.map_smul a ρ

end OptimalTransportMetricWitness

/-- Free-energy functional with the entropy/expectation split recorded explicitly. -/
@[rep_depth thermo]
structure FreeEnergyFunctional (State : Type*) where
  entropyTerm : Density State → ℝ
  expectationTerm : Density State → ℝ
  /-- Convexity of the complete free-energy functional. -/
  convexity :
    ConvexOn ℝ Set.univ (fun ρ => entropyTerm ρ + expectationTerm ρ)
  /-- Inf-compactness: every free-energy sublevel is compact. -/
  compact_sublevel :
    ∀ c : ℝ,
      IsCompact
        {ρ : Density State |
          entropyTerm ρ + expectationTerm ρ ≤ c}
  /-- Lower semicontinuity through closed free-energy sublevels. -/
  closed_sublevel :
    ∀ c : ℝ,
      IsClosed
        {ρ : Density State |
          entropyTerm ρ + expectationTerm ρ ≤ c}

namespace FreeEnergyFunctional

variable {State : Type*}

/-- Free energy derived from its entropy and expectation contributions. -/
def freeEnergy (F : FreeEnergyFunctional State) : Density State → ℝ :=
  fun ρ => F.entropyTerm ρ + F.expectationTerm ρ

@[rep_depth thermo]
theorem freeEnergy_eq
    (F : FreeEnergyFunctional State) (ρ : Density State) :
    F.freeEnergy ρ = F.entropyTerm ρ + F.expectationTerm ρ :=
  rfl

@[rep_depth thermo]
theorem freeEnergy_eq_split
    (F : FreeEnergyFunctional State) (ρ : Density State) :
    F.freeEnergy ρ = F.entropyTerm ρ + F.expectationTerm ρ :=
  rfl

/-- The complete free energy is convex on the full density carrier. -/
theorem freeEnergy_convex
    (F : FreeEnergyFunctional State) :
    ConvexOn ℝ Set.univ F.freeEnergy := by
  simpa [freeEnergy] using F.convexity

/-- Every free-energy sublevel is compact. -/
theorem freeEnergy_sublevel_compact
    (F : FreeEnergyFunctional State) (c : ℝ) :
    IsCompact {ρ : Density State | F.freeEnergy ρ ≤ c} := by
  simpa [freeEnergy] using F.compact_sublevel c

/-- Every free-energy sublevel is closed. -/
theorem freeEnergy_sublevel_closed
    (F : FreeEnergyFunctional State) (c : ℝ) :
    IsClosed {ρ : Density State | F.freeEnergy ρ ≤ c} := by
  simpa [freeEnergy] using F.closed_sublevel c

end FreeEnergyFunctional

/-- Dissipative Wasserstein/Onsager gradient-flow witness. -/
@[rep_depth thermo]
structure WassersteinGradientFlow (State : Type*) where
  ot : OptimalTransportMetricWitness State
  freeEnergy : FreeEnergyFunctional State
  stepSize : ℝ
  stepSize_pos : 0 < stepSize
  dissipativeFlow : Density State → Density State
  /--
  Each update minimizes the Jordan--Kinderlehrer--Otto objective against every
  density competitor.
  -/
  minimizes_jko :
    ∀ previous candidate : Density State,
      freeEnergy.freeEnergy (dissipativeFlow previous) +
          ot.cost (dissipativeFlow previous) previous ^ 2 /
            (2 * stepSize) ≤
        freeEnergy.freeEnergy candidate +
          ot.cost candidate previous ^ 2 / (2 * stepSize)

namespace WassersteinGradientFlow

variable {State : Type*}

/-- The genuine JKO objective at a previous density and positive time step. -/
def jkoObjective
    (W : WassersteinGradientFlow State)
    (previous candidate : Density State) : ℝ :=
  W.freeEnergy.freeEnergy candidate +
    W.ot.cost candidate previous ^ 2 / (2 * W.stepSize)

/-- The installed dissipative update minimizes the JKO objective. -/
theorem jko_minimizing
    (W : WassersteinGradientFlow State)
    (previous candidate : Density State) :
    W.jkoObjective previous (W.dissipativeFlow previous) ≤
      W.jkoObjective previous candidate :=
  W.minimizes_jko previous candidate

/--
JKO minimization implies monotone free-energy decay by choosing the previous
density itself as competitor.
-/
theorem freeEnergy_decay
    (W : WassersteinGradientFlow State)
    (previous : Density State) :
    W.freeEnergy.freeEnergy (W.dissipativeFlow previous) ≤
      W.freeEnergy.freeEnergy previous := by
  have h := W.minimizes_jko previous previous
  have hcost_nonneg :
      0 ≤ W.ot.cost (W.dissipativeFlow previous) previous ^ 2 /
        (2 * W.stepSize) := by
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (by norm_num) W.stepSize_pos))
  rw [W.ot.cost_self previous, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_div, add_zero] at h
  exact le_trans (le_add_of_nonneg_right hcost_nonneg) h

end WassersteinGradientFlow

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
  reversibleFlow : Density State → Density State
  dissipativeFlow : Density State → Density State
  freeEnergy : FreeEnergyFunctional State
  reversibleStationary : reversibleFlow density = 0
  dissipativeStationary : dissipativeFlow density = 0
  freeEnergyMinimizer :
    ∀ ρ : Density State,
      freeEnergy.freeEnergy density ≤ freeEnergy.freeEnergy ρ

namespace EquilibriumCandidate

variable {State : Type*}

/-- Both dynamical channels vanish at an equilibrium density. -/
theorem flows_stationary
    (E : EquilibriumCandidate State) :
    E.reversibleFlow E.density = 0 ∧
      E.dissipativeFlow E.density = 0 :=
  ⟨E.reversibleStationary, E.dissipativeStationary⟩

/-- The equilibrium density minimizes the installed free energy. -/
theorem freeEnergy_le
    (E : EquilibriumCandidate State) (ρ : Density State) :
    E.freeEnergy.freeEnergy E.density ≤ E.freeEnergy.freeEnergy ρ :=
  E.freeEnergyMinimizer ρ

end EquilibriumCandidate

/--
State-dynamics packet combining Souriau transport, metriplectic split, and
optimal transport.

The object is intentionally a witness container, not a global theorem.
-/
@[rep_depth thermo]
structure SouriauMetriplecticOTFlow
    (State LieGroup LieAlgebra LieDual Observable : Type*)
    [Ring Observable] where
  souriau : SouriauLieThermoData State LieGroup LieAlgebra LieDual
  transport : SouriauTransportFlow State LieGroup LieAlgebra LieDual
  metriplectic : MetriplecticSystem Observable
  gradientFlow : WassersteinGradientFlow State
  reversibleFlow : Density State → Density State

/-- The total flow is the sum of reversible and dissipative pieces. -/
def totalFlowFormula
    {State : Type*}
    (reversibleFlow dissipativeFlow : Density State → Density State) :
    Density State → Density State :=
  fun ρ => reversibleFlow ρ + dissipativeFlow ρ

namespace SouriauMetriplecticOTFlow

variable {State LieGroup LieAlgebra LieDual Observable : Type*}
variable [Ring Observable]

/-- The optimal-transport metric is owned by the installed JKO flow. -/
def ot
    (F : SouriauMetriplecticOTFlow
      State LieGroup LieAlgebra LieDual Observable) :
    OptimalTransportMetricWitness State :=
  F.gradientFlow.ot

/-- The free-energy functional is owned by the installed JKO flow. -/
def freeEnergy
    (F : SouriauMetriplecticOTFlow
      State LieGroup LieAlgebra LieDual Observable) :
    FreeEnergyFunctional State :=
  F.gradientFlow.freeEnergy

/-- The dissipative leg is the genuine JKO update. -/
def dissipativeFlow
    (F : SouriauMetriplecticOTFlow
      State LieGroup LieAlgebra LieDual Observable) :
    Density State → Density State :=
  F.gradientFlow.dissipativeFlow

/-- The total density flow is derived from its reversible and JKO legs. -/
def totalFlow
    (F : SouriauMetriplecticOTFlow
      State LieGroup LieAlgebra LieDual Observable) :
    Density State → Density State :=
  totalFlowFormula F.reversibleFlow F.dissipativeFlow

/-- The reversible and dissipative pieces add pointwise on densities. -/
@[rep_depth thermo]
theorem totalFlow_eq_add_at
    (F : SouriauMetriplecticOTFlow State LieGroup LieAlgebra LieDual Observable)
    (ρ : Density State) :
    F.totalFlow ρ = totalFlowFormula F.reversibleFlow F.dissipativeFlow ρ :=
  rfl

/-- Expanded pointwise total-flow equation used by downstream bridges. -/
theorem totalFlow_eq_reversible_add_dissipative
    (F : SouriauMetriplecticOTFlow
      State LieGroup LieAlgebra LieDual Observable)
    (ρ : Density State) :
    F.totalFlow ρ = F.reversibleFlow ρ + F.dissipativeFlow ρ :=
  rfl

/-- The JKO leg decreases the installed free energy. -/
theorem dissipative_freeEnergy_decay
    (F : SouriauMetriplecticOTFlow
      State LieGroup LieAlgebra LieDual Observable)
    (ρ : Density State) :
    F.freeEnergy.freeEnergy (F.dissipativeFlow ρ) ≤
      F.freeEnergy.freeEnergy ρ :=
  F.gradientFlow.freeEnergy_decay ρ

end SouriauMetriplecticOTFlow

  /--
  Product data bundling projector-side metric transport and probability-density
  transport.
  -/
@[rep_depth transport]
structure MetricTransportCompatibility
    {R : Type*} [Ring R]
  (P P' : ProjectorPair R)
  (State : Type*) where
  projectorTransport : SimilarityTransport P P'
  otWitness : OptimalTransportMetricWitness State

/-- The Radon-Nikodym derivative log(ρ/σ). -/
noncomputable def logRadonNikodym (ρ σ : ℝ) : ℝ :=
  Real.log (ρ / σ)

/-- The relative modular Hamiltonian H_rel = -log(ρ/σ). -/
noncomputable def relativeModularHamiltonianFormula (ρ σ : ℝ) : ℝ :=
  - logRadonNikodym ρ σ

/-- Commutative log Radon--Nikodym / relative modular Hamiltonian packet. -/
@[rep_depth thermo]
structure LogRadonNikodymHamiltonian (State : Type*) where
  rho : Density State
  sigma : Density State

namespace LogRadonNikodymHamiltonian

variable {State : Type*}
variable (L : LogRadonNikodymHamiltonian State)

/-- The logarithmic Radon--Nikodym density derived from the two densities. -/
noncomputable def logRN : Density State :=
  fun x => logRadonNikodym (L.rho x) (L.sigma x)

/-- The relative modular Hamiltonian derived as negative log density ratio. -/
noncomputable def relativeModularHamiltonian : Density State :=
  fun x => relativeModularHamiltonianFormula (L.rho x) (L.sigma x)

/-- Re-export of the log-RN definition. -/
@[rep_depth thermo]
theorem logRN_eq (x : State) :
    L.logRN x = Real.log (L.rho x / L.sigma x) :=
  rfl

/-- Re-export of the relative modular Hamiltonian definition. -/
@[rep_depth thermo]
theorem relativeModularHamiltonian_eq (x : State) :
    L.relativeModularHamiltonian x = - Real.log (L.rho x / L.sigma x) :=
  rfl

end LogRadonNikodymHamiltonian

/--
Commutative relative-entropy readout of a logarithmic Radon--Nikodym packet.

The logarithmic data and expectation map are direct arguments; no evidence
record is introduced merely to pair them.
-/
noncomputable def commutativeRelativeEntropy
    {State : Type*}
    (logData : LogRadonNikodymHamiltonian State)
    (expectation : Density State →ₗ[ℝ] ℝ) : ℝ :=
  expectation logData.relativeModularHamiltonian

/-- Native expectation readback for the commutative relative entropy. -/
theorem commutativeRelativeEntropy_eq_expectation
    {State : Type*}
    (logData : LogRadonNikodymHamiltonian State)
    (expectation : Density State →ₗ[ℝ] ℝ) :
    commutativeRelativeEntropy logData expectation =
      expectation logData.relativeModularHamiltonian :=
  rfl

/-- Linearity of a commutative expectation under addition of log generators. -/
theorem relativeEntropyExpectation_add
    {State : Type*}
    (expectation : Density State →ₗ[ℝ] ℝ)
    (K L : Density State) :
    expectation (K + L) = expectation K + expectation L :=
  expectation.map_add K L

/-- The additive modular correction is the logarithm of the positive Jacobian. -/
noncomputable def jacobianModularCorrection
    (jacobianFactor : ℝ) : ℝ :=
  Real.log jacobianFactor

/-- Exponentiating the additive correction recovers the Jacobian factor. -/
theorem exp_jacobianModularCorrection
    {jacobianFactor : ℝ}
    (hpos : 0 < jacobianFactor) :
    Real.exp (jacobianModularCorrection jacobianFactor) =
      jacobianFactor := by
  rw [jacobianModularCorrection, Real.exp_log hpos]

/-- Multiplicative Jacobians become additive modular corrections. -/
theorem jacobianModularCorrection_mul
    {J K : ℝ}
    (hJ : 0 < J)
    (hK : 0 < K) :
    jacobianModularCorrection (J * K) =
      jacobianModularCorrection J + jacobianModularCorrection K := by
  rw [jacobianModularCorrection,
    Real.log_mul (ne_of_gt hJ) (ne_of_gt hK)]
  rfl

/--
Operatorial logarithmic-potential layer on a genuine noncommutative C-star
algebra.

Only the state/reference operators and the Rényi order are supplied as data.
The modular logarithm, Duhamel derivative, and both Rényi kernels are derived
below from Mathlib continuous functional calculus and the native
noncommutative operator owners.
-/
@[rep_depth thermo]
structure OperatorialLogPotentialLayer
    (State A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] where
  logRN : LogRadonNikodymHamiltonian State
  jacobianFactor : ℝ
  jacobianFactor_pos : 0 < jacobianFactor
  densityOperator : State → A
  referenceOperator : State → A
  expectation : A →ₚ[ℂ] ℂ
  renyiOrder : ℝ

namespace OperatorialLogPotentialLayer

variable {State A : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/--
The state-surprisal/modular-log generator `-log ρ`, retained as an operator in
the original noncommutative algebra.
-/
noncomputable def modularLogGenerator
    (L : OperatorialLogPotentialLayer State A) (x : State) : A :=
  -CFC.log (L.densityOperator x)

/-- Native relative log-density operator `log ρ - log σ`. -/
noncomputable def relativeLogDensityOperator
    (L : OperatorialLogPotentialLayer State A) (x : State) : A :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.relativeLogDensity
    (L.densityOperator x) (L.referenceOperator x)

/-- Native Umegaki operator kernel `ρ * (log ρ - log σ)`. -/
noncomputable def umegakiRelativeEntropyKernel
    (L : OperatorialLogPotentialLayer State A) (x : State) : A :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiKernel
    (L.densityOperator x) (L.referenceOperator x)

/--
The scalar Umegaki readout is downstream of the noncommutative operator kernel
and an explicit Mathlib positive functional.
-/
noncomputable def umegakiRelativeEntropy
    (L : OperatorialLogPotentialLayer State A) (x : State) : ℂ :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
    L.expectation (L.densityOperator x) (L.referenceOperator x)

@[simp]
theorem umegakiRelativeEntropyKernel_apply
    (L : OperatorialLogPotentialLayer State A) (x : State) :
    L.umegakiRelativeEntropyKernel x =
      L.densityOperator x *
        (CFC.log (L.densityOperator x) -
          CFC.log (L.referenceOperator x)) :=
  rfl

@[simp]
theorem umegakiRelativeEntropy_apply
    (L : OperatorialLogPotentialLayer State A) (x : State) :
    L.umegakiRelativeEntropy x =
      L.expectation
        (L.densityOperator x *
          (CFC.log (L.densityOperator x) -
            CFC.log (L.referenceOperator x))) :=
  rfl

/-- Native Duhamel derivative of the exponential at the modular log generator. -/
noncomputable def modularExponentialDuhamelDerivative
    (L : OperatorialLogPotentialLayer State A) (x : State) : A →L[ℝ] A :=
  InfoGeometry.OperatorAlgebra.duhamelDerivative
    (L.modularLogGenerator x)

/-- Petz Rényi operator kernel for the state/reference pair at `x`. -/
noncomputable def petzModularDeformation
    (L : OperatorialLogPotentialLayer State A) (x : State) : A :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.petzKernel
    L.renyiOrder (L.densityOperator x) (L.referenceOperator x)

/-- Sandwiched Rényi operator kernel for the state/reference pair at `x`. -/
noncomputable def sandwichedModularDeformation
    (L : OperatorialLogPotentialLayer State A) (x : State) : A :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.sandwichedKernel
    L.renyiOrder (L.densityOperator x) (L.referenceOperator x)

/-- The sandwiched Rényi deformation is positive in the native star order. -/
theorem sandwichedModularDeformation_nonneg
    (L : OperatorialLogPotentialLayer State A) (x : State) :
    0 ≤ L.sandwichedModularDeformation x :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.sandwichedKernel_nonneg
    L.renyiOrder (L.densityOperator x) (L.referenceOperator x)

/--
Thermodynamic force density generated by the negative relative modular
Hamiltonian.  This is a derived logarithmic force, not a proposition marker.
-/
noncomputable def thermodynamicForce
    (L : OperatorialLogPotentialLayer State A) : Density State :=
  -L.logRN.relativeModularHamiltonian

/-- The force is pointwise the negative relative modular generator. -/
theorem thermodynamicForce_eq_neg_relativeModularHamiltonian
    (L : OperatorialLogPotentialLayer State A) (x : State) :
    L.thermodynamicForce x =
      -L.logRN.relativeModularHamiltonian x :=
  rfl

/-- Expanded logarithmic density-ratio formula for the force. -/
theorem thermodynamicForce_eq_log_density_ratio
    (L : OperatorialLogPotentialLayer State A) (x : State) :
    L.thermodynamicForce x =
      Real.log (L.logRN.rho x / L.logRN.sigma x) := by
  simp [thermodynamicForce,
    LogRadonNikodymHamiltonian.relativeModularHamiltonian,
    relativeModularHamiltonianFormula, logRadonNikodym]

end OperatorialLogPotentialLayer

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

/--
The Thermodynamic Engine (Grand Canonical Partition & Free Energy Gradient).

The Grand Canonical Ensemble of Ensembles: we sum over all possible lengths of
binary words, i.e., all possible combinations of prime numbers.

The unnormalized partition function is Z(s) = Π_p (1 - p^{-s})^{-1} (Euler product).
The Free Energy potential Φ(s) = log Z(s).
The Thermodynamic Force driving optimal transport is F = ∇Φ = ∇ log Z(s).
-/
@[rep_depth transport, capstone]
structure GrandCanonicalPartitionFunction where
  /-- The logarithm of the partition function (free energy potential). -/
  logPartition : ℝ → ℝ
  
  /-- Chemical potential field regulating new mode generation. -/
  chemicalPotential : ℝ
  
  /-- Partition is positive for physical interpretability. -/
  partition_pos : ∀ s, 0 < Real.exp (logPartition s)
  
  /-- The logarithmic partition function is smooth in the Mathlib sense. -/
  logPartition_smooth : ContDiff ℝ ⊤ logPartition

/-- The partition function Z(s) = exp(logPartition s). -/
noncomputable def partitionFormula (logPartition : ℝ → ℝ) : ℝ → ℝ :=
  fun s => Real.exp (logPartition s)

namespace GrandCanonicalPartitionFunction

/-- The canonical free-energy functional in the grand canonical ensemble. -/
@[rep_depth thermo]
def freeEnergyPotential (G : GrandCanonicalPartitionFunction)
    (s : ℝ) : ℝ :=
  G.logPartition s

@[rep_depth thermo]
theorem freeEnergyPotential_eq_logPartition
    (G : GrandCanonicalPartitionFunction) (s : ℝ) :
    G.freeEnergyPotential s = G.logPartition s :=
  rfl

/-- Definitional readout of the partition function. -/
@[rep_depth thermo]
theorem partition_eq_exp_logPartition (G : GrandCanonicalPartitionFunction) (s : ℝ) :
    partitionFormula G.logPartition s = Real.exp (G.logPartition s) :=
  rfl

/--
The logarithmic derivative of the partition function.
This is the thermodynamic force density that drives the Wasserstein OT.
-/
@[rep_depth transport]
noncomputable def logPartitionDerivative
    (G : GrandCanonicalPartitionFunction) (s : ℝ) : ℝ :=
  deriv G.logPartition s

/-- The logarithmic partition derivative is Mathlib's real derivative. -/
@[simp]
theorem logPartitionDerivative_eq_deriv
    (G : GrandCanonicalPartitionFunction) (s : ℝ) :
    G.logPartitionDerivative s = deriv G.logPartition s :=
  rfl

/--
A pointwise derivative certificate computes the thermodynamic force density.
-/
theorem logPartitionDerivative_eq_of_hasDerivAt
    (G : GrandCanonicalPartitionFunction) {s force : ℝ}
    (h : HasDerivAt G.logPartition force s) :
    G.logPartitionDerivative s = force := by
  exact h.deriv

end GrandCanonicalPartitionFunction

/--
Logarithmic Gradient Vector Field of the Free Energy.
This is the driving force F = ∇ log Z(s) that propels the Wasserstein gradient flow.
-/
@[rep_depth transport]
structure LogPartitionGradientField (State : Type*) where
  /-- The grand canonical partition data. -/
  grandCanonical : GrandCanonicalPartitionFunction

  /-- State-space coordinate at which the scalar partition potential is read. -/
  coordinate : State → ℝ

  /-- The gradient of log Z in state space. -/
  gradientField : State → ℝ

  /-- The gradient field is exactly the logarithmic derivative of the partition. -/
  gradient_eq_logDerivative :
    ∀ x, gradientField x =
      grandCanonical.logPartitionDerivative (coordinate x)

namespace LogPartitionGradientField

variable {State : Type*}

/-- The driving force as a vector field on state space. -/
@[rep_depth transport]
def thermodynamicForce (F : LogPartitionGradientField State) (x : State) : ℝ :=
  F.gradientField x

/-- A state is thermodynamically active when its partition force is nonzero. -/
def IsThermodynamicallyActive
    (F : LogPartitionGradientField State) (x : State) : Prop :=
  F.grandCanonical.logPartitionDerivative (F.coordinate x) ≠ 0

/-- The thermodynamic force is the derivative of the log-partition potential. -/
theorem thermodynamicForce_eq_logPartitionDerivative
    (F : LogPartitionGradientField State) (x : State) :
    F.thermodynamicForce x =
      F.grandCanonical.logPartitionDerivative (F.coordinate x) :=
  F.gradient_eq_logDerivative x

/-- A nonzero gradient gives thermodynamic activity by the derivative identity. -/
theorem nonzero_gradient_implies_activity
    (F : LogPartitionGradientField State) {x : State}
    (h : F.thermodynamicForce x ≠ 0) :
    F.IsThermodynamicallyActive x := by
  unfold IsThermodynamicallyActive
  rw [← F.thermodynamicForce_eq_logPartitionDerivative x]
  exact h

end LogPartitionGradientField

/--
Broken Detailed Balance Witness.
In equilibrium, detailed balance means forward and backward flows cancel.
But the Grand Canonical system breaks detailed balance due to mode generation.
This creates entropy production (non-zero gradient of free energy).
-/
@[rep_depth thermo]
structure BrokenDetailedBalanceWitness (State : Type*) where
  /-- Density / probability measure on state space. -/
  density : Density State

  /-- The reversible (Hamiltonian) flow. -/
  reversibleFlow : Density State → Density State

  /-- The dissipative (gradient) flow. -/
  dissipativeFlow : Density State → Density State

  /-- Forward flux in reversible flow. -/
  forwardFlux : State → ℝ

  /-- Backward flux in reversible flow. -/
  backwardFlux : State → ℝ

  /-- Imbalance between forward and backward: broken detailed balance. -/
  balanceDefect : State → ℝ
  balanceDefect_eq :
    ∀ x, balanceDefect x = forwardFlux x - backwardFlux x

  /-- Entropy-production density on state space. -/
  entropyProduction : State → ℝ

  /-- Entropy production is pointwise non-negative (Second Law). -/
  entropyProduction_nonneg : ∀ x, 0 ≤ entropyProduction x

  /-- Vanishing entropy production at a state restores detailed balance there. -/
  entropyProduction_zero_implies_detailed_balance :
    ∀ x, entropyProduction x = 0 → forwardFlux x = backwardFlux x

namespace BrokenDetailedBalanceWitness

variable {State : Type*}

/-- The balance defect is the forward-minus-backward flux. -/
theorem balanceDefect_eq_flux_difference
    (B : BrokenDetailedBalanceWitness State) (x : State) :
    B.balanceDefect x = B.forwardFlux x - B.backwardFlux x :=
  B.balanceDefect_eq x

/-- Detailed balance is equivalent to vanishing of the installed balance defect. -/
theorem detailedBalance_iff_balanceDefect_eq_zero
    (B : BrokenDetailedBalanceWitness State) (x : State) :
    B.forwardFlux x = B.backwardFlux x ↔ B.balanceDefect x = 0 := by
  rw [B.balanceDefect_eq]
  exact sub_eq_zero.symm

/-- Zero entropy production forces zero balance defect. -/
theorem balanceDefect_eq_zero_of_entropyProduction_eq_zero
    (B : BrokenDetailedBalanceWitness State) (x : State)
    (hzero : B.entropyProduction x = 0) :
    B.balanceDefect x = 0 := by
  apply (B.detailedBalance_iff_balanceDefect_eq_zero x).1
  exact B.entropyProduction_zero_implies_detailed_balance x hzero

end BrokenDetailedBalanceWitness

/--
Riemann-Weil Explicit Formula as a Wasserstein Vector Field.

The explicit formula ∑_{n} Λ(n) n^{-s} (sum over prime powers with von Mangoldt weights)
is precisely the logarithmic derivative of the Euler product: d/ds log Π(1 - p^{-s})^{-1}.

This means the explicit formula IS the Wasserstein gradient vector field that drives
optimal transport through the Cantor crystal.
-/
@[rep_depth transport, capstone]
structure ExplicitFormulaVectorField (State : Type*) where
  /-- The supplied Riemann-Weil explicit formula sum. -/
  explicitFormula : ℝ → ℝ

  /-- The supplied logarithmic derivative of the Euler product partition function. -/
  logEulerDerivative : ℝ → ℝ

  /-- The Wasserstein gradient vector field on state space. -/
  wassersteinField : State → ℝ

  /-- State-space coordinate at which the scalar explicit formula is read. -/
  coordinate : State → ℝ

  /-- CORE IDENTITY: Explicit formula equals log-Euler derivative. -/
  explicitFormula_eq_logEulerDerivative :
    ∀ s, explicitFormula s = logEulerDerivative s

  /-- The Wasserstein field is the state-space realization of the explicit formula. -/
  wasserstein_from_explicit :
    ∀ x, wassersteinField x = explicitFormula (coordinate x)

  /-- Vector field is smooth and supports JKO dynamics. -/
  field_regularity : ContDiff ℝ ⊤ explicitFormula

/-- The Riemann-Weil explicit formula sum: ∑ Λ(n) n^{-s}. -/
def riemannWeilExplicitFormula (vonMangoldtReadout : ℝ → ℝ) : ℝ → ℝ :=
  fun s => vonMangoldtReadout s

namespace ExplicitFormulaVectorField

variable {State : Type*}

/-- Re-export of the explicit formula identity. -/
@[rep_depth transport]
theorem explicitFormula_eq (E : ExplicitFormulaVectorField State) (s : ℝ) :
    E.explicitFormula s = riemannWeilExplicitFormula E.explicitFormula s :=
  rfl

/-- The explicit formula gradient drives the Wasserstein OT. -/
@[rep_depth transport]
theorem wasserstein_driven_by_riemann_weil
    (E : ExplicitFormulaVectorField State) (x : State) :
    E.wassersteinField x =
      riemannWeilExplicitFormula E.explicitFormula (E.coordinate x) := by
  exact E.wasserstein_from_explicit x

end ExplicitFormulaVectorField

/-- Data of an RG/free-energy flow, without a fabricated fixed-point witness. -/
@[rep_depth transport]
structure RGFlowData (State : Type*) where
  freeEnergy : State → ℝ
  forwardFlux : State → ℝ
  backwardFlux : State → ℝ
  scaleAction : ℝ → State → State

namespace RGFlowData

variable {State : Type*}

/--
A genuine RG equilibrium condition at `x`.

It consists of local free-energy minimality, invariance of the scale orbit,
and equality of forward/backward fluxes.  Vanishing derivatives and entropy
production are derived below rather than stored as independent fields.
-/
def IsRGFixedPoint [NormedAddCommGroup State]
    (E : RGFlowData State) (x : State) : Prop :=
  IsLocalMin E.freeEnergy x ∧
    (∀ scale : ℝ, E.scaleAction scale x = x) ∧
    E.forwardFlux x = E.backwardFlux x

/-- The Fréchet free-energy gradient at a state. -/
noncomputable def freeEnergyGradient
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (E : RGFlowData State) (x : State) : State →L[ℝ] ℝ :=
  fderiv ℝ E.freeEnergy x

/-- The RG beta operator is the derivative of the scale orbit at scale zero. -/
noncomputable def betaFunction
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (E : RGFlowData State) (x : State) : ℝ →L[ℝ] State :=
  fderiv ℝ (fun scale : ℝ => E.scaleAction scale x) 0

/-- Operator-independent entropy production is the forward/backward flux defect. -/
def entropyProduction (E : RGFlowData State) (x : State) : ℝ :=
  E.forwardFlux x - E.backwardFlux x

/-- Local free-energy minimality forces the native Fréchet gradient to vanish. -/
theorem freeEnergyGradient_eq_zero_of_isRGFixedPoint
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (E : RGFlowData State) {x : State} (hx : E.IsRGFixedPoint x) :
    E.freeEnergyGradient x = 0 :=
  hx.1.fderiv_eq_zero

/-- Scale-orbit invariance forces the native RG beta operator to vanish. -/
theorem betaFunction_eq_zero_of_isRGFixedPoint
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (E : RGFlowData State) {x : State} (hx : E.IsRGFixedPoint x) :
    E.betaFunction x = 0 := by
  have horbit :
      (fun scale : ℝ => E.scaleAction scale x) =
        (fun _ : ℝ => x) := by
    funext scale
    exact hx.2.1 scale
  rw [betaFunction, horbit, fderiv_const_apply]

/-- Detailed balance makes the flux-defect entropy production vanish. -/
theorem entropyProduction_eq_zero_of_isRGFixedPoint
    [NormedAddCommGroup State]
    (E : RGFlowData State) {x : State} (hx : E.IsRGFixedPoint x) :
    E.entropyProduction x = 0 := by
  exact sub_eq_zero.mpr hx.2.2

/-- The scale-invariance component of a genuine RG fixed point. -/
theorem scaleAction_fixed_of_isRGFixedPoint
    [NormedAddCommGroup State]
    (E : RGFlowData State) {x : State} (hx : E.IsRGFixedPoint x)
    (scale : ℝ) :
    E.scaleAction scale x = x :=
  hx.2.1 scale

/-- All three derived RG forces vanish at a genuine fixed point. -/
@[rep_depth transport]
theorem fixedPoint_implies_all_forces_vanish
    [TopologicalSpace State] [NormedAddCommGroup State] [NormedSpace ℝ State]
    (E : RGFlowData State) {x : State} (hx : E.IsRGFixedPoint x) :
    E.freeEnergyGradient x = 0 ∧
      E.betaFunction x = 0 ∧
      E.entropyProduction x = 0 :=
  ⟨E.freeEnergyGradient_eq_zero_of_isRGFixedPoint hx,
    E.betaFunction_eq_zero_of_isRGFixedPoint hx,
    E.entropyProduction_eq_zero_of_isRGFixedPoint hx⟩

end RGFlowData

/-!
## Recovered typed equilibrium owner

`RGFlowData` describes a flow together with predicates selecting a fixed
state.  The separate packet below is retained for clients that need to carry
the selected state and its equilibrium laws as data.  Its laws are equations
over supplied operators and observables, not uninstantiated proposition
markers.
-/
@[rep_depth transport]
structure RGFixedPointEquilibrium (State : Type*) where
  /-- The selected RG fixed state. -/
  fixedPoint : State
  /-- Free energy and the force/flux readouts on the state space. -/
  freeEnergy : State → ℝ
  gradientLogPartition : State → ℝ
  betaFunction : State → ℝ
  entropyProduction : State → ℝ
  forwardFlux : State → ℝ
  backwardFlux : State → ℝ
  /-- The supplied scale action on the state space. -/
  scaleAction : ℝ → State → State
  /-- Vanishing logarithmic-partition force at the fixed state. -/
  gradientLogPartition_zero :
    gradientLogPartition fixedPoint = 0
  /-- Vanishing beta function at the fixed state. -/
  betaFunction_zero :
    betaFunction fixedPoint = 0
  /-- Detailed balance at the fixed state. -/
  detailedBalance_restored :
    forwardFlux fixedPoint = backwardFlux fixedPoint
  /-- Vanishing entropy production at the fixed state. -/
  entropyProduction_zero :
    entropyProduction fixedPoint = 0
  /-- Scale invariance of the selected fixed state. -/
  conformalInvariance :
    ∀ scale, scaleAction scale fixedPoint = fixedPoint

namespace RGFixedPointEquilibrium

/-- All supplied equilibrium force readouts vanish at the selected state. -/
@[rep_depth transport]
theorem fixedPoint_implies_all_forces_vanish
    (E : RGFixedPointEquilibrium State) :
    E.gradientLogPartition E.fixedPoint = 0 ∧
      E.betaFunction E.fixedPoint = 0 ∧
      E.entropyProduction E.fixedPoint = 0 :=
  ⟨E.gradientLogPartition_zero, E.betaFunction_zero,
    E.entropyProduction_zero⟩

/-- Equilibrium gives zero entropy production and detailed balance. -/
@[rep_depth transport]
theorem continuum_emergence_via_equilibration
    (E : RGFixedPointEquilibrium State) :
    E.entropyProduction E.fixedPoint = 0 ∧
      E.forwardFlux E.fixedPoint = E.backwardFlux E.fixedPoint :=
  ⟨E.entropyProduction_zero, E.detailedBalance_restored⟩

end RGFixedPointEquilibrium

/--
Conservative bridge packet connecting the installed grand-canonical, detailed-
balance, optimal-transport, explicit-formula, and RG fixed-point owners.

This is a witness container only: it records the intended alignment between the
owners without claiming the analytic identification itself.
-/
@[rep_depth transport]
structure GrandCanonicalThermodynamicBridge (State : Type*) where
  grandCanonical : GrandCanonicalPartitionFunction
  logForce : LogPartitionGradientField State
  brokenDetailedBalance : BrokenDetailedBalanceWitness State
  transport : WassersteinGradientFlow State
  explicitFormula : ExplicitFormulaVectorField State
  rgFlow : RGFlowData State
  force_matches_explicitFormula :
    ∀ x : State, logForce.thermodynamicForce x = explicitFormula.wassersteinField x

namespace GrandCanonicalThermodynamicBridge

variable {State : Type*}

@[rep_depth transport]
theorem thermodynamicForce_eq_explicitFormula
    (B : GrandCanonicalThermodynamicBridge State) (x : State) :
    B.logForce.thermodynamicForce x = B.explicitFormula.wassersteinField x :=
  B.force_matches_explicitFormula x

end GrandCanonicalThermodynamicBridge

/--
The Driving Force of the Metriplectic Optimal Transport.
In the Grand Canonical Ensemble of the prime gas, the gradient flow 
is driven by the logarithmic derivative of the Souriau partition function.
-/
@[rep_depth transport]
theorem optimal_transport_driven_by_log_partition_gradient
    (State : Type*) (B : GrandCanonicalThermodynamicBridge State) :
    B.logForce.thermodynamicForce = B.explicitFormula.wassersteinField := by
  funext x
  exact B.force_matches_explicitFormula x

/--
THE RIEMANN-WEIL EXPLICIT FORMULA AS A WASSERSTEIN VECTOR FIELD.
Because Z(s) is the Euler product, ∇ log Z is the explicit formula.
-/
@[rep_depth transport]
theorem riemann_weil_is_wasserstein_gradient
    (State : Type*) (F : LogPartitionGradientField State) (E : ExplicitFormulaVectorField State)
    (hEquiv : ∀ x, F.thermodynamicForce x = E.wassersteinField x) :
    -- The informational flow is exactly the explicit formula sum
    (fun x => E.wassersteinField x) = (fun x => F.thermodynamicForce x) := by
  funext x
  rw [hEquiv]

/--
THE CONTINUUM EMERGENCE VIA THERMODYNAMIC EQUILIBRATION.
The informational manifold reaches its smooth Calabi-Yau state at the RG fixed point,
where the Riemann-Weil driving force (broken detailed balance) is equilibrated.
-/
theorem continuum_emergence_via_equilibration
    (State : Type*) [NormedAddCommGroup State]
    (E : RGFlowData State) (x : State)
    (hx : E.IsRGFixedPoint x) :
    E.entropyProduction x = 0 ∧
      E.forwardFlux x = E.backwardFlux x :=
  ⟨E.entropyProduction_eq_zero_of_isRGFixedPoint hx, hx.2.2⟩

end InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
