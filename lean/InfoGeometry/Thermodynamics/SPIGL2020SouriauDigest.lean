import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
open InfoGeometry.Algebraic.CartanExponentialFamily
open InfoGeometry.Thermodynamics.FiniteGibbsRelative
open InfoGeometry.Thermodynamics.FiniteConnesCocycle
open InfoGeometry.Analysis

/-! ## 1. Operatorial Souriau thermodynamics -/

theorem entropy_eq_expectation_modularPotential
    {State LieAlgebra LieDual : Type*}
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) :
    D.entropy = D.expectationBeta D.modularPotential :=
  SouriauNegativeLogRNDerivative.entropy_eq_expectation_modularPotential D

theorem souriauEntropy_eq_Phi_add_pairing_Q_beta
    {State LieAlgebra LieDual : Type*}
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) :
    D.entropy = D.souriau.partitionPotential + D.souriau.pairing D.Q D.souriau.beta :=
  SouriauNegativeLogRNDerivative.souriauEntropy_eq_Phi_add_pairing_Q_beta D

theorem firstVariation_eq_negative_pairing_Q
    {State LieAlgebra LieDual : Type*}
    (M : MomentMapGeneratingPotential State LieAlgebra LieDual)
    (δβ : LieAlgebra) :
    M.dPhi δβ = -M.souriau.pairing M.Q δβ :=
  MomentMapGeneratingPotential.firstVariation_eq_negative_pairing_Q M δβ

theorem secondVariation_eq_covariance
    {State LieAlgebra LieDual : Type*}
    (M : MomentMapGeneratingPotential State LieAlgebra LieDual)
    (ξ η : LieAlgebra) :
    M.hessian ξ η = M.covarianceTensor ξ η :=
  MomentMapGeneratingPotential.secondVariation_eq_covariance M ξ η

theorem KL_eq_souriau_Bregman
    {State LieAlgebra LieDual : Type*}
    (B : SouriauKLBregmanWitness State LieAlgebra LieDual) :
    B.klValue =
      B.alphaPartitionPotential
      - B.generator.souriau.partitionPotential
      - B.generator.dPhi B.alphaMinusBeta :=
  SouriauKLBregmanWitness.KL_eq_souriau_Bregman B

theorem relativeEntropy_eq_expectation_difference
    {State LieAlgebra LieDual : Type*}
    (B : SouriauKLBregmanWitness State LieAlgebra LieDual) :
    B.klValue =
      B.alphaPartitionPotential
      - B.generator.souriau.partitionPotential
      - B.generator.dPhi B.alphaMinusBeta :=
  SouriauKLBregmanWitness.relativeEntropy_eq_expectation_difference B

theorem partitionPotential_eq_log_trace_theorem
    {Param Op : Type*}
    (E : OperatorialExponentialFamily Param Op)
    (β : Param) :
    E.partitionPotential β = Real.log (E.traceReadout (E.untracedExponential β)) :=
  OperatorialExponentialFamily.partitionPotential_eq_log_trace_theorem E β

theorem K_beta_eq_pairing_apply
    {State LieAlgebra LieDual : Type*}
    (D : SouriauLieThermoData State LieAlgebra LieDual)
    (x : State) :
    D.K_beta x = D.pairing (D.momentMap x) D.beta :=
  SouriauLieThermoData.K_beta_eq_pairing_apply D x

theorem gibbsDensity_eq_exp_neg_pairing_sub_Phi
    {State LieAlgebra LieDual : Type*}
    (D : SouriauLieThermoData State LieAlgebra LieDual)
    (x : State) :
    D.gibbsDensity x =
      Real.exp (-D.pairing (D.momentMap x) D.beta - D.partitionPotential) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    SouriauLieThermoData.gibbsDensity_eq_exp_neg_pairing_sub_Phi D x

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
structure FiniteSouriauStageData (State LieAlgebra LieDual : Type*) where
  thermo : SouriauLieThermoData State LieAlgebra LieDual
  rn : SouriauNegativeLogRNDerivative State LieAlgebra LieDual
  moment : MomentMapGeneratingPotential State LieAlgebra LieDual
  bregman : SouriauKLBregmanWitness State LieAlgebra LieDual

namespace FiniteSouriauStageData

variable {State LieAlgebra LieDual : Type*}

@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (D : FiniteSouriauStageData State LieAlgebra LieDual) :
    D.rn.entropy = D.rn.expectationBeta D.rn.modularPotential :=
  SouriauNegativeLogRNDerivative.entropy_eq_expectation_modularPotential D.rn

@[rep_depth thermo]
theorem souriauEntropy_eq_Phi_add_pairing_Q_beta
    (D : FiniteSouriauStageData State LieAlgebra LieDual) :
    D.rn.entropy =
      D.rn.souriau.partitionPotential + D.rn.souriau.pairing D.rn.Q D.rn.souriau.beta :=
  SouriauNegativeLogRNDerivative.souriauEntropy_eq_Phi_add_pairing_Q_beta D.rn

@[rep_depth thermo]
theorem firstVariation_eq_negative_pairing_Q
    (D : FiniteSouriauStageData State LieAlgebra LieDual)
    (δβ : LieAlgebra) :
    D.moment.dPhi δβ = -D.moment.souriau.pairing D.moment.Q δβ :=
  MomentMapGeneratingPotential.firstVariation_eq_negative_pairing_Q D.moment δβ

@[rep_depth thermo]
theorem secondVariation_eq_covariance
    (D : FiniteSouriauStageData State LieAlgebra LieDual)
    (ξ η : LieAlgebra) :
    D.moment.hessian ξ η = D.moment.covarianceTensor ξ η :=
  MomentMapGeneratingPotential.secondVariation_eq_covariance D.moment ξ η

@[rep_depth thermo]
theorem KL_eq_souriau_Bregman
    (D : FiniteSouriauStageData State LieAlgebra LieDual) :
    D.bregman.klValue =
      D.bregman.alphaPartitionPotential
      - D.bregman.generator.souriau.partitionPotential
      - D.bregman.generator.dPhi D.bregman.alphaMinusBeta :=
  SouriauKLBregmanWitness.KL_eq_souriau_Bregman D.bregman

@[rep_depth thermo]
theorem relativeEntropy_eq_expectation_difference
    (D : FiniteSouriauStageData State LieAlgebra LieDual) :
    D.bregman.klValue =
      D.bregman.alphaPartitionPotential
      - D.bregman.generator.souriau.partitionPotential
      - D.bregman.generator.dPhi D.bregman.alphaMinusBeta :=
  SouriauKLBregmanWitness.relativeEntropy_eq_expectation_difference D.bregman

@[rep_depth thermo]
theorem K_beta_eq_pairing_apply
    (D : FiniteSouriauStageData State LieAlgebra LieDual)
    (x : State) :
    D.thermo.K_beta x = D.thermo.pairing (D.thermo.momentMap x) D.thermo.beta :=
  SouriauLieThermoData.K_beta_eq_pairing_apply D.thermo x

@[rep_depth thermo]
theorem gibbsDensity_eq_exp_neg_pairing_sub_Phi
    (D : FiniteSouriauStageData State LieAlgebra LieDual)
    (x : State) :
    D.thermo.gibbsDensity x =
      Real.exp (-D.thermo.pairing (D.thermo.momentMap x) D.thermo.beta
        - D.thermo.partitionPotential) :=
  SouriauLieThermoData.gibbsDensity_eq_exp_neg_pairing_sub_Phi D.thermo x

end FiniteSouriauStageData

/--
Finite-stage tower seed for an eventual inductive colimit.

The tower is deliberately lightweight: it stores a stagewise family of finite
Souriau packets.  A future bonding/colimit module can add the actual
compatibility maps without changing the finite owner data.
-/
structure FiniteSouriauTowerSeed (State LieAlgebra LieDual : Type*) where
  stage : ℕ → FiniteSouriauStageData State LieAlgebra LieDual

namespace FiniteSouriauTowerSeed

variable {State LieAlgebra LieDual : Type*}

@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (T : FiniteSouriauTowerSeed State LieAlgebra LieDual) (n : ℕ) :
    (T.stage n).rn.entropy =
      (T.stage n).rn.expectationBeta (T.stage n).rn.modularPotential :=
  (T.stage n).entropy_eq_expectation_modularPotential

@[rep_depth thermo]
theorem souriauEntropy_eq_Phi_add_pairing_Q_beta
    (T : FiniteSouriauTowerSeed State LieAlgebra LieDual) (n : ℕ) :
    (T.stage n).rn.entropy =
      (T.stage n).rn.souriau.partitionPotential
      + (T.stage n).rn.souriau.pairing (T.stage n).rn.Q (T.stage n).rn.souriau.beta :=
  (T.stage n).souriauEntropy_eq_Phi_add_pairing_Q_beta

@[rep_depth thermo]
theorem K_beta_eq_pairing_apply
    (T : FiniteSouriauTowerSeed State LieAlgebra LieDual) (n : ℕ) (x : State) :
    (T.stage n).thermo.K_beta x =
      (T.stage n).thermo.pairing ((T.stage n).thermo.momentMap x)
        (T.stage n).thermo.beta :=
  (T.stage n).K_beta_eq_pairing_apply x

@[rep_depth thermo]
theorem gibbsDensity_eq_exp_neg_pairing_sub_Phi
    (T : FiniteSouriauTowerSeed State LieAlgebra LieDual) (n : ℕ) (x : State) :
    (T.stage n).thermo.gibbsDensity x =
      Real.exp
        (- (T.stage n).thermo.pairing ((T.stage n).thermo.momentMap x)
            (T.stage n).thermo.beta
          - (T.stage n).thermo.partitionPotential) :=
  (T.stage n).gibbsDensity_eq_exp_neg_pairing_sub_Phi x

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
  flow : InfoGeometry.Topology.ThermodynamicGauge.CausalNonequilibriumFlow Op
  trace : Op →ₗ[ℝ] ℝ
  pathPacket : InfoGeometry.Topology.MaximumCaliberPath.MaximumCaliberPacket Op
  pathPacket_flow_eq : pathPacket.flow = flow

namespace FiniteSouriauDynamicsStageData

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

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
