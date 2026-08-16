import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Algebraic.CartanExponentialFamily
import InfoGeometry.Thermodynamics.FiniteGibbsRelative
import InfoGeometry.Thermodynamics.FiniteConnesCocycle
import InfoGeometry.Physics.SouriauMassieuPlanckFunctional
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.MaximumCaliberPath
import InfoGeometry.Analysis.SouriauThermodynamics
import InfoGeometry.Analysis.SouriauCocycle

/-!
# SPIGL 2020 Souriau digest

This file is a theorem-honest digest of the formulas extracted from
`Barbaresco-SPILG2020.pdf`.

It does not introduce a new theory layer.  It re-exports the owner theorems
already proved in the repository for:

* Souriau entropy as an expectation of the modular potential;
* the Massieu / Gibbs / moment-map identities;
* first and second variations of the potential;
* finite Cartan relative entropy and Fisher covariance formulas;
* finite Connes cocycle laws in the commuting scalar shadow;
* the finite Laplace-transform convexity baseline;
* the `J^2 = -I` symplectic carrier.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.SPIGL2020SouriauDigest

open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Canonical.NativeOperatorialExponentialFamily
open InfoGeometry.Algebraic.CartanExponentialFamily
open InfoGeometry.Thermodynamics.FiniteGibbsRelative
open InfoGeometry.Thermodynamics.FiniteConnesCocycle
open InfoGeometry.Analysis

/-! ## 1. Operatorial Souriau thermodynamics -/

theorem entropy_eq_expectation_modularPotential
    {State LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    (D : OperatorialRNDatum State LieAlgebra Obs) :
    D.entropy = D.expectation D.modularPotential :=
  OperatorialRNDatum.entropy_eq_expectation_modularPotential D

theorem secondVariation_eq_bkmCovariance
    {Param Obs : Type*} [AddMonoid Param]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    (M : OperatorialMomentGeneratingPotential Param Obs)
    (β : Param) (A B : Obs) :
    M.covarianceTensor β A B = M.bkmCovariance β A B :=
  OperatorialMomentGeneratingPotential.covarianceTensor_eq_bkmCovariance M β A B

theorem partitionPotential_eq_log_trace_theorem
    {Param Op : Type*} [AddMonoid Param]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]
    (E : Family Param Op)
    (β : Param) :
    Real.log (E.partitionFunction β) =
      Real.log (E.traceReadout (E.untracedExponential β)) := by
  rfl

theorem K_beta_eq_operatorial_firstMoment
    {State LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    (D : OperatorialSouriauStateData State LieAlgebra Obs)
    (x : State) :
    D.K_beta x = D.family.traceReadout (D.family.Khat_beta * D.observable x) :=
  rfl

theorem gibbsDensity_eq_exp_neg_K_beta_sub_Phi
    {State LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    (D : OperatorialSouriauStateData State LieAlgebra Obs)
    (x : State) :
    D.gibbsDensity x =
      Real.exp (-D.K_beta x - D.partitionPotential) :=
  D.gibbsDensity_eq_exp_neg_K_beta_sub_partitionPotential x

/-! ## 2. Finite Cartan / Fisher / Connes shadows -/

theorem relativeEntropy_eq_massieuBregman
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ η : FiniteTemperature ι) (hZ : 0 < Z θ) :
    relativeEntropy θ η = massieuBregman θ η :=
  FiniteGibbsRelative.relativeEntropy_eq_massieuBregman θ η hZ

theorem fisherMetric_eq_covariance
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : FiniteTemperature ι) (X Y : ι → ℝ) (hZ : 0 < Z θ) :
    fisherMetric θ X Y =
      expect θ (fun i => X i * Y i) - expect θ X * expect θ Y :=
  FiniteGibbsRelative.fisherMetric_eq_covariance θ X Y hZ

theorem massieuBregman_self
    {ι : Type*} [Fintype ι]
    (θ : FiniteTemperature ι) :
    massieuBregman θ θ = 0 :=
  FiniteGibbsRelative.massieuBregman_self θ

theorem relativeEntropy_self
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : FiniteTemperature ι) (hZ : 0 < Z θ) :
    relativeEntropy θ θ = 0 :=
  FiniteGibbsRelative.relativeEntropy_self θ hZ

theorem finiteConnesFlux_cocycle
    {G : Type*} [Group G]
    (Uψ Uφ : ℝ → G)
    (hψ_add : ∀ s t : ℝ, Uψ (s + t) = Uψ s * Uψ t)
    (hφ_add : ∀ s t : ℝ, Uφ (s + t) = Uφ s * Uφ t)
    (s t : ℝ) :
    Uψ (s + t) * (Uφ (s + t))⁻¹ =
      (Uψ s * (Uφ s)⁻¹) *
        (Uφ s * (Uψ t * (Uφ t)⁻¹) * (Uφ s)⁻¹) :=
  FiniteConnesCocycle.finiteConnesFlux_cocycle Uψ Uφ hψ_add hφ_add s t

theorem finitePositiveDensityRatioAtTime_add
    {ι : Type*}
    (ΔK : ι → ℝ) (s t : ℝ) (i : ι) :
    finitePositiveDensityRatioAtTime ΔK (s + t) i =
      finitePositiveDensityRatioAtTime ΔK s i *
        finitePositiveDensityRatioAtTime ΔK t i :=
  FiniteConnesCocycle.finitePositiveDensityRatioAtTime_add ΔK s t i

theorem finiteCommutingConnesPhase_add_time
    {ι : Type*}
    (ΔK : ι → ℝ) (s t : ℝ) (i : ι) :
    finiteCommutingConnesPhase ΔK (s + t) i =
      finiteCommutingConnesPhase ΔK s i *
        finiteCommutingConnesPhase ΔK t i :=
  FiniteConnesCocycle.finiteCommutingConnesPhase_add_time ΔK s t i

/-! ## 3. Souriau/Koszul/Fisher and symplectic baseline -/

theorem J_matrix_sq_eq_neg_one_digest :
    J_matrix * J_matrix = - (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  InfoGeometry.Analysis.J_matrix_sq_eq_neg_one

theorem zero_symplectic_2_cocycle_jacobi_identity_digest
    (X Y Z : SL2cAlgebra) :
    zero_symplectic_2_cocycle X Y +
      zero_symplectic_2_cocycle Y Z +
      zero_symplectic_2_cocycle Z X = 0 :=
  InfoGeometry.Analysis.zero_symplectic_2_cocycle_jacobi_identity X Y Z

/-! ## 4. Finite-stage digest packet for the inductive tower -/

/--
Finite Souriau stage data.

This is the minimal finite-dimensional carrier that can be placed stagewise in
an eventual inductive tower.  It does not assert any bonding compatibility by
itself; it only packages the finite owner structures already proved in the
repository.
-/
structure FiniteSouriauStageData
    (State LieAlgebra LieDual Obs : Type*)
    [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] where
  thermo : OperatorialSouriauStateData State LieAlgebra Obs
  rn : OperatorialRNDatum State LieAlgebra Obs
  moment : OperatorialMomentGeneratingPotential LieAlgebra Obs

namespace FiniteSouriauStageData

variable {State LieAlgebra LieDual Obs : Type*} [AddMonoid LieAlgebra]
variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (D : FiniteSouriauStageData State LieAlgebra LieDual Obs) :
    D.rn.entropy = D.rn.expectation D.rn.modularPotential :=
  OperatorialRNDatum.entropy_eq_expectation_modularPotential D.rn

@[rep_depth thermo]
theorem secondVariation_eq_bkmCovariance
    (D : FiniteSouriauStageData State LieAlgebra LieDual Obs)
    (β : LieAlgebra) (A B : Obs) :
    D.moment.covarianceTensor β A B = D.moment.bkmCovariance β A B :=
  OperatorialMomentGeneratingPotential.covarianceTensor_eq_bkmCovariance
    D.moment β A B

@[rep_depth thermo]
theorem K_beta_eq_operatorial_firstMoment
    (D : FiniteSouriauStageData State LieAlgebra LieDual Obs)
    (x : State) :
    D.thermo.K_beta x =
      D.thermo.family.traceReadout (D.thermo.family.Khat_beta * D.thermo.observable x) :=
  rfl

@[rep_depth thermo]
theorem gibbsDensity_eq_exp_neg_K_beta_sub_Phi
    (D : FiniteSouriauStageData State LieAlgebra LieDual Obs)
    (x : State) :
    D.thermo.gibbsDensity x =
      Real.exp (-D.thermo.K_beta x - D.thermo.partitionPotential) :=
  D.thermo.gibbsDensity_eq_exp_neg_K_beta_sub_partitionPotential x

end FiniteSouriauStageData

/--
Finite-stage tower seed for an eventual inductive colimit.

The tower is deliberately lightweight: it stores a stagewise family of finite
Souriau packets.  A future bonding/colimit module can add the actual
compatibility maps without changing the finite owner data.
-/
abbrev FiniteSouriauTowerSeed
    (State LieAlg LieDual Obs : Type*) [AddMonoid LieAlg]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] :=
  ℕ → FiniteSouriauStageData State LieAlg LieDual Obs

namespace FiniteSouriauTowerSeed

variable {State LieAlg LieDual Obs : Type*} [AddMonoid LieAlg]
variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

abbrev stage
    (T : FiniteSouriauTowerSeed State LieAlg LieDual Obs) :
    ℕ → FiniteSouriauStageData State LieAlg LieDual Obs :=
  T

end FiniteSouriauTowerSeed

namespace FiniteSouriauTowerSeed

variable {State LieAlgebra LieDual Obs : Type*} [AddMonoid LieAlgebra]
variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (T : FiniteSouriauTowerSeed State LieAlgebra LieDual Obs) (n : ℕ) :
    (T.stage n).rn.entropy =
      (T.stage n).rn.expectation (T.stage n).rn.modularPotential :=
  (T.stage n).entropy_eq_expectation_modularPotential

@[rep_depth thermo]
theorem K_beta_eq_operatorial_firstMoment
    (T : FiniteSouriauTowerSeed State LieAlgebra LieDual Obs) (n : ℕ) (x : State) :
    (T.stage n).thermo.K_beta x =
      (T.stage n).thermo.family.traceReadout
        ((T.stage n).thermo.family.Khat_beta * (T.stage n).thermo.observable x) :=
  rfl

@[rep_depth thermo]
theorem gibbsDensity_eq_exp_neg_K_beta_sub_Phi
    (T : FiniteSouriauTowerSeed State LieAlgebra LieDual Obs) (n : ℕ) (x : State) :
    (T.stage n).thermo.gibbsDensity x =
      Real.exp
        (- (T.stage n).thermo.K_beta x
          - (T.stage n).thermo.partitionPotential) :=
  (T.stage n).gibbsDensity_eq_exp_neg_K_beta_sub_Phi x

end FiniteSouriauTowerSeed

/-! ## 5. Finite Gibbs / gauge / caliber stage packet -/

/--
Finite Souriau dynamics stage data.

This packages the finite Gibbs readouts, the finite thermodynamic gauge flow,
and the finite maximum-caliber path packet.  It is the finite-dimensional layer
that can later be fed into an inductive tower with bonding maps.
-/
structure FiniteSouriauDynamicsStageData (ι : Type*) [Fintype ι] [Nonempty ι]
    (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  beta : ℝ
  energy : ι → ℝ
  trace : Op →ₗ[ℝ] ℝ
  pathPacket : InfoGeometry.Topology.MaximumCaliberPath.MaximumCaliberPacket Op

namespace FiniteSouriauDynamicsStageData

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-- The stage flow is the flow carried by its maximum-caliber path packet. -/
abbrev flow (D : FiniteSouriauDynamicsStageData ι Op) := D.pathPacket.flow

/-- The stage flow agrees definitionally with the path-packet flow. -/
theorem pathPacket_flow_eq (D : FiniteSouriauDynamicsStageData ι Op) :
    D.pathPacket.flow = D.flow := by
  rfl

@[rep_depth thermo]
theorem souriauPartition_pos (D : FiniteSouriauDynamicsStageData ι Op) :
    0 < Physics.SouriauMassieuPlanckFunctional.souriauPartition D.beta D.energy :=
  Physics.SouriauMassieuPlanckFunctional.souriauPartition_pos D.beta D.energy

@[rep_depth thermo]
theorem gibbsWeight_sum_eq_one (D : FiniteSouriauDynamicsStageData ι Op) :
    (∑ i : ι,
      Physics.SouriauMassieuPlanckFunctional.gibbsWeight D.beta D.energy i) = 1 :=
  Physics.SouriauMassieuPlanckFunctional.gibbsWeight_sum_eq_one D.beta D.energy

@[rep_depth thermo]
theorem boltzmannEntropy_gibbsWeight_eq_massieu_add_beta_meanEnergy
    (D : FiniteSouriauDynamicsStageData ι Op) :
    Physics.SouriauMassieuPlanckFunctional.boltzmannEntropy
        (Physics.SouriauMassieuPlanckFunctional.gibbsWeight D.beta D.energy) =
      Physics.SouriauMassieuPlanckFunctional.massieuPlanckPotential D.beta D.energy +
        D.beta *
          Physics.SouriauMassieuPlanckFunctional.meanEnergy D.beta D.energy :=
  Physics.SouriauMassieuPlanckFunctional.boltzmannEntropy_gibbsWeight_eq_massieu_add_beta_meanEnergy
    D.beta D.energy

@[rep_depth thermo]
theorem scalarBregman_self (phi gradPhi : ℝ → ℝ) (x : ℝ) :
    Physics.SouriauMassieuPlanckFunctional.scalarBregman phi gradPhi x x = 0 :=
  Physics.SouriauMassieuPlanckFunctional.scalarBregman_self phi gradPhi x

@[rep_depth thermo]
theorem entropy_production_eq_commutator
    (D : FiniteSouriauDynamicsStageData ι Op) :
    InfoGeometry.Topology.ThermodynamicGauge.entropy_production D.flow =
      D.flow.P_forward * D.flow.P_backward - D.flow.P_backward * D.flow.P_forward :=
  InfoGeometry.Topology.ThermodynamicGauge.entropy_production_eq_commutator D.flow

@[rep_depth thermo]
theorem entropy_production_eq_zero_iff_detailed_balance
    (D : FiniteSouriauDynamicsStageData ι Op) :
    InfoGeometry.Topology.ThermodynamicGauge.entropy_production D.flow = 0 ↔
      D.flow.P_forward * D.flow.P_backward = D.flow.P_backward * D.flow.P_forward :=
  InfoGeometry.Topology.ThermodynamicGauge.entropy_production_eq_zero_iff_detailed_balance
    D.flow

@[rep_depth thermo]
theorem pathEntropy_eq_zero_of_detailed_balance
    (D : FiniteSouriauDynamicsStageData ι Op)
    (hdb : InfoGeometry.Topology.ThermodynamicGauge.entropy_production D.flow = 0) :
    D.pathPacket.pathEntropy = 0 :=
  by
    have hdb' : InfoGeometry.Topology.ThermodynamicGauge.entropy_production D.pathPacket.flow = 0 := by
      simpa [D.pathPacket_flow_eq] using hdb
    exact
      InfoGeometry.Topology.MaximumCaliberPath.MaximumCaliberPacket.pathEntropy_eq_zero_of_detailed_balance
        D.pathPacket hdb'

@[rep_depth thermo]
theorem caliber_eq_zero_of_detailed_balance
    (D : FiniteSouriauDynamicsStageData ι Op)
    (hdb : InfoGeometry.Topology.ThermodynamicGauge.entropy_production D.flow = 0) :
    D.pathPacket.caliber = 0 :=
  by
    have hdb' : InfoGeometry.Topology.ThermodynamicGauge.entropy_production D.pathPacket.flow = 0 := by
      simpa [D.pathPacket_flow_eq] using hdb
    exact
      InfoGeometry.Topology.MaximumCaliberPath.MaximumCaliberPacket.caliber_eq_zero_of_detailed_balance
        D.pathPacket hdb'

@[rep_depth thermo]
theorem finiteConnesFlux_cocycle
    (D : FiniteSouriauDynamicsStageData ι Op)
    {G : Type*} [Group G]
    (Uψ Uφ : ℝ → G)
    (hψ_add : ∀ s t : ℝ, Uψ (s + t) = Uψ s * Uψ t)
    (hφ_add : ∀ s t : ℝ, Uφ (s + t) = Uφ s * Uφ t)
    (s t : ℝ) :
    Uψ (s + t) * (Uφ (s + t))⁻¹ =
      (Uψ s * (Uφ s)⁻¹) *
        (Uφ s * (Uψ t * (Uφ t)⁻¹) * (Uφ s)⁻¹) :=
  FiniteConnesCocycle.finiteConnesFlux_cocycle Uψ Uφ hψ_add hφ_add s t

@[rep_depth thermo]
theorem finitePositiveDensityRatioAtTime_add
    (D : FiniteSouriauDynamicsStageData ι Op)
    (ΔK : ι → ℝ) (s t : ℝ) (i : ι) :
    FiniteConnesCocycle.finitePositiveDensityRatioAtTime ΔK (s + t) i =
      FiniteConnesCocycle.finitePositiveDensityRatioAtTime ΔK s i *
        FiniteConnesCocycle.finitePositiveDensityRatioAtTime ΔK t i :=
  FiniteConnesCocycle.finitePositiveDensityRatioAtTime_add ΔK s t i

@[rep_depth thermo]
theorem finiteCommutingConnesPhase_add_time
    (D : FiniteSouriauDynamicsStageData ι Op)
    (ΔK : ι → ℝ) (s t : ℝ) (i : ι) :
    FiniteConnesCocycle.finiteCommutingConnesPhase ΔK (s + t) i =
      FiniteConnesCocycle.finiteCommutingConnesPhase ΔK s i *
        FiniteConnesCocycle.finiteCommutingConnesPhase ΔK t i :=
  FiniteConnesCocycle.finiteCommutingConnesPhase_add_time ΔK s t i

@[rep_depth thermo]
theorem pathEntropy_eq_curvatureTrace
    (D : FiniteSouriauDynamicsStageData ι Op) :
    D.pathPacket.pathEntropy =
      D.pathPacket.trace
        (InfoGeometry.Topology.ThermodynamicGauge.thermodynamic_curvature D.pathPacket.flow) :=
  D.pathPacket.pathEntropy_eq_curvatureTrace

end FiniteSouriauDynamicsStageData

end InfoGeometry.Thermodynamics.SPIGL2020SouriauDigest
