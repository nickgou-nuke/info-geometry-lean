import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Thermodynamics.FiniteGibbsRelative
import InfoGeometry.Thermodynamics.FiniteConnesCocycle
import InfoGeometry.Physics.SouriauMassieuPlanckFunctional
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.MaximumCaliberPath
import InfoGeometry.Prequantum.Scaling
import InfoGeometry.Prequantum.Bundle

/-!
# MDPAS JMSouriau digest

Finite theorem-honest digest of Souriau's 1974 spin-particle paper
`Modèle de particule à spin dans le champ électromagnétique et gravitationnel`.

The module only packages finite formulas already owned elsewhere in the repo:

* operatorial Souriau entropy / modular-potential identities;
* finite Gibbs / Massieu / Fisher readouts;
* finite Connes-cocycle multiplicativity;
* finite thermodynamic-gauge and maximum-caliber readbacks;
* scalarized prequantum scaling laws.

It does not assert the global field-equation, foliation, or full quantization
theorems of the paper.  Those remain future owner layers.
-/

noncomputable section

namespace InfoGeometry.Physics.MDPASJMSouriauDigest

open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Algebraic.CartanExponentialFamily
open InfoGeometry.Thermodynamics.FiniteGibbsRelative
open InfoGeometry.Thermodynamics.FiniteConnesCocycle
open InfoGeometry.Physics.SouriauMassieuPlanckFunctional
open InfoGeometry.Topology.ThermodynamicGauge
open InfoGeometry.Topology.MaximumCaliberPath
open InfoGeometry.Prequantum

/-! ## 5. Finite-stage carrier for future colimit transport -/

structure FiniteMDPASJMStageData
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (Op : Type*) [Ring Op] [Algebra ℝ Op]
    (State LieAlgebra LieDual : Type*) where
  thermo : SouriauLieThermoData State LieAlgebra LieDual
  rn : SouriauNegativeLogRNDerivative State LieAlgebra LieDual
  moment : MomentMapGeneratingPotential State LieAlgebra LieDual
  bregman : SouriauKLBregmanWitness State LieAlgebra LieDual
  pathPacket : MaximumCaliberPacket Op
  prequantum : PrequantumData

namespace FiniteMDPASJMStageData

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable {State LieAlgebra LieDual : Type*}

/-- The stage flow is the flow carried by its maximum-caliber path packet. -/
abbrev flow
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual) :=
  D.pathPacket.flow

/-- The stage flow agrees definitionally with the path-packet flow. -/
theorem pathPacket_flow_eq
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual) :
    D.pathPacket.flow = D.flow := by
  rfl

@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual) :
    D.rn.entropy = D.rn.expectationBeta D.rn.modularPotential :=
  D.rn.entropy_eq_expectation_modularPotential

@[rep_depth thermo]
theorem souriauEntropy_eq_Phi_add_pairing_Q_beta
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual) :
    D.rn.entropy =
      D.rn.souriau.partitionPotential + D.rn.souriau.pairing D.rn.Q D.rn.souriau.beta :=
  D.rn.souriauEntropy_eq_Phi_add_pairing_Q_beta

@[rep_depth thermo]
theorem firstVariation_eq_negative_pairing_Q
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual)
    (δβ : LieAlgebra) :
    D.moment.dPhi δβ = -D.moment.souriau.pairing D.moment.Q δβ :=
  D.moment.firstVariation_eq_negative_pairing_Q δβ

@[rep_depth thermo]
theorem secondVariation_eq_covariance
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual)
    (ξ η : LieAlgebra) :
    D.moment.hessian ξ η = D.moment.covarianceTensor ξ η :=
  D.moment.secondVariation_eq_covariance ξ η

@[rep_depth thermo]
theorem KL_eq_souriau_Bregman
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual) :
    D.bregman.klValue =
      D.bregman.alphaPartitionPotential
      - D.bregman.generator.souriau.partitionPotential
      - D.bregman.generator.dPhi D.bregman.alphaMinusBeta :=
  D.bregman.KL_eq_souriau_Bregman

@[rep_depth thermo]
theorem relativeEntropy_eq_expectation_difference
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual) :
    D.bregman.klValue =
      D.bregman.alphaPartitionPotential
      - D.bregman.generator.souriau.partitionPotential
      - D.bregman.generator.dPhi D.bregman.alphaMinusBeta :=
  D.bregman.relativeEntropy_eq_expectation_difference

@[rep_depth thermo]
theorem pathEntropy_eq_zero_of_detailed_balance
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual)
    (hdb : entropy_production D.flow = 0) :
    D.pathPacket.pathEntropy = 0 :=
  have hdb' : entropy_production D.pathPacket.flow = 0 := by
    simpa [D.pathPacket_flow_eq] using hdb
  D.pathPacket.pathEntropy_eq_zero_of_detailed_balance hdb'

@[rep_depth thermo]
theorem caliber_eq_zero_of_detailed_balance
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual)
    (hdb : entropy_production D.flow = 0) :
    D.pathPacket.caliber = 0 :=
  have hdb' : entropy_production D.pathPacket.flow = 0 := by
    simpa [D.pathPacket_flow_eq] using hdb
  D.pathPacket.caliber_eq_zero_of_detailed_balance hdb'

@[rep_depth thermo]
theorem pathEntropy_eq_curvatureTrace
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual) :
    D.pathPacket.pathEntropy = D.pathPacket.trace (thermodynamic_curvature D.pathPacket.flow) :=
  D.pathPacket.pathEntropy_eq_curvatureTrace

@[rep_depth thermo]
theorem prequantum_connectionScale_smul
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual)
    (u : PrequantumData.Gauge) :
    PrequantumData.connectionScale (u • D.prequantum) =
      PrequantumData.connectionScale D.prequantum / (u : ℝ) :=
  PrequantumData.connectionScale_smul u D.prequantum

@[rep_depth thermo]
theorem prequantum_covariantScale_smul
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual)
    (u : PrequantumData.Gauge) :
    PrequantumData.covariantScale (u • D.prequantum) =
      PrequantumData.covariantScale D.prequantum :=
  PrequantumData.covariantScale_smul u D.prequantum

@[rep_depth thermo]
theorem prequantum_holonomyScale_eq_omega_over_hbar
    (D : FiniteMDPASJMStageData ι Op State LieAlgebra LieDual) :
    D.prequantum.holonomyScale = D.prequantum.omegaScale / D.prequantum.hbar :=
  PrequantumData.holonomyScale_eq_omega_over_hbar D.prequantum

end FiniteMDPASJMStageData

/-- A finite tower is natively a stage-indexed family.

No additional law is carried at this level; stage-specific laws are already
fields of `FiniteMDPASJMStageData`.
-/
abbrev FiniteMDPASJMTowerSeed
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (Op : Type*) [Ring Op] [Algebra ℝ Op]
    (State LieAlgebra LieDual : Type*) :=
  ℕ → FiniteMDPASJMStageData ι Op State LieAlgebra LieDual

abbrev FiniteMDPASJMTowerSeed.stage
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    {State LieAlgebra LieDual : Type*}
    (T : FiniteMDPASJMTowerSeed ι Op State LieAlgebra LieDual) :
    ℕ → FiniteMDPASJMStageData ι Op State LieAlgebra LieDual := T

namespace FiniteMDPASJMTowerSeed

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable {State LieAlgebra LieDual : Type*}

@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (T : FiniteMDPASJMTowerSeed ι Op State LieAlgebra LieDual) (n : ℕ) :
    (T.stage n).rn.entropy = (T.stage n).rn.expectationBeta (T.stage n).rn.modularPotential :=
  (T.stage n).entropy_eq_expectation_modularPotential

@[rep_depth thermo]
theorem pathEntropy_eq_curvatureTrace
    (T : FiniteMDPASJMTowerSeed ι Op State LieAlgebra LieDual) (n : ℕ) :
    (T.stage n).pathPacket.pathEntropy =
      (T.stage n).pathPacket.trace
        (thermodynamic_curvature (T.stage n).pathPacket.flow) :=
  (T.stage n).pathPacket.pathEntropy_eq_curvatureTrace

@[rep_depth thermo]
theorem prequantum_covariantScale_smul
    (T : FiniteMDPASJMTowerSeed ι Op State LieAlgebra LieDual)
    (n : ℕ) (u : PrequantumData.Gauge) :
    PrequantumData.covariantScale (u • (T.stage n).prequantum) =
      PrequantumData.covariantScale (T.stage n).prequantum :=
  (T.stage n).prequantum_covariantScale_smul u

end FiniteMDPASJMTowerSeed

/-! ## 6. Genuine direct-limit carrier for compatible finite towers -/

/-- Stage-tagged operator carrier used to build the algebraic direct limit. -/
structure MDPASJMStageCarrier (Op : Type*) where
  stage : ℕ
  value : Op

/--
A finite-stage tower equipped with one-step bonding ring homomorphisms.
The compatibility fields are concrete equations over the finite data, not an
opaque constructor-selectable proposition: the bonding maps must carry each flow component at stage
`n` to the corresponding component at stage `n+1`.
-/
structure FiniteMDPASJMDirectSystem
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (Op : Type*) [Ring Op] [Algebra ℝ Op]
    (State LieAlgebra LieDual : Type*) where
  tower : FiniteMDPASJMTowerSeed ι Op State LieAlgebra LieDual
  bond : ℕ → Op →+* Op
  map_Q : ∀ n, bond n (tower.stage n).flow.Q = (tower.stage (n + 1)).flow.Q
  map_d_ln_Q : ∀ n, bond n (tower.stage n).flow.d_ln_Q = (tower.stage (n + 1)).flow.d_ln_Q
  map_P_forward : ∀ n, bond n (tower.stage n).flow.P_forward =
    (tower.stage (n + 1)).flow.P_forward
  map_P_backward : ∀ n, bond n (tower.stage n).flow.P_backward =
    (tower.stage (n + 1)).flow.P_backward

namespace FiniteMDPASJMDirectSystem

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable {State LieAlgebra LieDual : Type*}

/-- One-step relation generating the direct-limit quotient. -/
inductive OneStep (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) :
    MDPASJMStageCarrier Op → MDPASJMStageCarrier Op → Prop where
  | bond (n : ℕ) (x : Op) :
      OneStep T ⟨n + 1, T.bond n x⟩ ⟨n, x⟩

/-- Setoid generated by the one-step bonding relation. -/
def directLimitSetoid (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) :
    Setoid (MDPASJMStageCarrier Op) where
  r := Relation.EqvGen (OneStep T)
  iseqv := Relation.EqvGen.is_equivalence (OneStep T)

/-- The genuine algebraic direct-limit carrier: finite stage elements modulo bonding. -/
def DirectLimitCarrier (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) : Type _ :=
  Quotient (directLimitSetoid T)

instance (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) :
    Inhabited (DirectLimitCarrier T) :=
  ⟨Quotient.mk (directLimitSetoid T) ⟨0, 0⟩⟩

/-- Canonical map from a finite stage into the direct-limit carrier. -/
def ofStage (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    (n : ℕ) (x : Op) : DirectLimitCarrier T :=
  Quotient.mk (directLimitSetoid T) ⟨n, x⟩

/-- The direct-limit quotient identifies a bonded element with its source. -/
theorem ofStage_bond
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    (n : ℕ) (x : Op) :
    ofStage T (n + 1) (T.bond n x) = ofStage T n x := by
  apply Quotient.sound
  let a : MDPASJMStageCarrier Op := { stage := n + 1, value := T.bond n x }
  let b : MDPASJMStageCarrier Op := { stage := n, value := x }
  change Relation.EqvGen (OneStep T) a b
  exact Relation.EqvGen.rel a b (OneStep.bond (T := T) n x)

/--
Recursor for maps out of the direct-limit carrier.

This is the quotient-level universal property: a family of maps from all finite
stages descends to the carrier exactly when it is compatible with every bonding
map.
-/
def directLimitLift
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {Y : Type*}
    (toLimit : ∀ _n : ℕ, Op → Y)
    (hbond : ∀ n x, toLimit (n + 1) (T.bond n x) = toLimit n x) :
    DirectLimitCarrier T → Y :=
  Quotient.lift
    (fun c : MDPASJMStageCarrier Op => toLimit c.stage c.value)
    (by
      intro a b h
      induction h with
      | rel x y hxy =>
          cases hxy with
          | bond n x => exact hbond n x
      | refl x => rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz)

@[simp] theorem directLimitLift_ofStage
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {Y : Type*}
    (toLimit : ∀ _n : ℕ, Op → Y)
    (hbond : ∀ n x, toLimit (n + 1) (T.bond n x) = toLimit n x)
    (n : ℕ) (x : Op) :
    directLimitLift T toLimit hbond (ofStage T n x) = toLimit n x :=
  rfl

theorem directLimitLift_unique
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {Y : Type*}
    (toLimit : ∀ _n : ℕ, Op → Y)
    (hbond : ∀ n x, toLimit (n + 1) (T.bond n x) = toLimit n x)
    (g : DirectLimitCarrier T → Y)
    (hg : ∀ n x, g (ofStage T n x) = toLimit n x) :
    g = directLimitLift T toLimit hbond := by
  funext z
  refine Quotient.inductionOn z ?_
  intro c
  cases c with
  | mk n x =>
      exact (hg n x).trans (directLimitLift_ofStage T toLimit hbond n x).symm

/--
The proper infinity-colimit theorem for the carrier: compatible cocones out of
all finite stages factor uniquely through `DirectLimitCarrier`.
-/
theorem directLimitCarrier_universal
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {Y : Type*}
    (toLimit : ∀ _n : ℕ, Op → Y)
    (hbond : ∀ n x, toLimit (n + 1) (T.bond n x) = toLimit n x) :
    ∃! lift : DirectLimitCarrier T → Y,
      ∀ n x, lift (ofStage T n x) = toLimit n x := by
  refine ⟨directLimitLift T toLimit hbond, ?_, ?_⟩
  · intro n x
    rfl
  · intro g hg
    exact directLimitLift_unique T toLimit hbond g hg

/-- Evaluation of a compatible cocone on stage-tagged representatives. -/
def stageEval
    {X : Type*} (φ : ∀ _n : ℕ, Op → X) : MDPASJMStageCarrier Op → X :=
  fun a => φ a.stage a.value

/-- A compatible cocone is constant on the generated direct-limit equivalence relation. -/
theorem stageEval_respects_eqvGen
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {X : Type*} (φ : ∀ _n : ℕ, Op → X)
    (hφ : ∀ n x, φ (n + 1) (T.bond n x) = φ n x) :
    ∀ {a b : MDPASJMStageCarrier Op},
      Relation.EqvGen (OneStep T) a b → stageEval φ a = stageEval φ b := by
  intro a b h
  induction h with
  | rel x y hxy =>
      cases hxy with
      | bond n x => exact hφ n x
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/--
Universal cocone map out of the genuine direct-limit carrier.
Any compatible family of stage maps `φ n : Op → X` descends to the quotient.
-/
def compatibleLift
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {X : Type*} (φ : ∀ _n : ℕ, Op → X)
    (hφ : ∀ n x, φ (n + 1) (T.bond n x) = φ n x) :
    DirectLimitCarrier T → X :=
  Quotient.lift (stageEval φ) (by
    intro a b h
    exact stageEval_respects_eqvGen T φ hφ h)

/-- The descended cocone map evaluates correctly on every finite stage. -/
theorem compatibleLift_ofStage
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {X : Type*} (φ : ∀ _n : ℕ, Op → X)
    (hφ : ∀ n x, φ (n + 1) (T.bond n x) = φ n x)
    (n : ℕ) (x : Op) :
    compatibleLift T φ hφ (ofStage T n x) = φ n x :=
  rfl

/-- Uniqueness of maps out of the direct limit from their values on finite stages. -/
theorem compatibleLift_unique
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {X : Type*} (φ : ∀ _n : ℕ, Op → X)
    (hφ : ∀ n x, φ (n + 1) (T.bond n x) = φ n x)
    (ψ : DirectLimitCarrier T → X)
    (hψ : ∀ n x, ψ (ofStage T n x) = φ n x) :
    ψ = compatibleLift T φ hφ := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  cases a with
  | mk n x =>
      exact (hψ n x).trans (compatibleLift_ofStage T φ hφ n x).symm

/--
The proper infinite inductive-colimit universal property for the MDPAS carrier:
the quotient carrier is nonempty, every compatible cocone descends to it, and
that descent is unique by finite-stage values.
-/
theorem infinite_inductive_colimit_universal_property
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual)
    {X : Type*} (φ : ∀ _n : ℕ, Op → X)
    (hφ : ∀ n x, φ (n + 1) (T.bond n x) = φ n x) :
    Nonempty (DirectLimitCarrier T) ∧
      ∃! Φ : DirectLimitCarrier T → X,
        ∀ n x, Φ (ofStage T n x) = φ n x := by
  refine ⟨⟨default⟩, compatibleLift T φ hφ, ?_, ?_⟩
  · intro n x
    exact compatibleLift_ofStage T φ hφ n x
  · intro Ψ hΨ
    exact compatibleLift_unique T φ hφ Ψ hΨ

/-- Bonding maps preserve the finite entropy-production commutator. -/
theorem bond_entropy_production
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    T.bond n (entropy_production (T.tower.stage n).flow) =
      entropy_production (T.tower.stage (n + 1)).flow := by
  simp [entropy_production, T.map_P_forward n, T.map_P_backward n]

/-- Bonding maps preserve the finite thermodynamic gauge connection. -/
theorem bond_thermodynamic_gauge_connection
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    T.bond n (thermodynamic_gauge_connection (T.tower.stage n).flow) =
      thermodynamic_gauge_connection (T.tower.stage (n + 1)).flow := by
  simp [thermodynamic_gauge_connection, T.map_P_forward n, T.map_P_backward n,
    T.map_d_ln_Q n]

/-- Bonding maps preserve the finite thermodynamic curvature word. -/
theorem bond_thermodynamic_curvature
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    T.bond n (thermodynamic_curvature (T.tower.stage n).flow) =
      thermodynamic_curvature (T.tower.stage (n + 1)).flow := by
  simp [thermodynamic_curvature, bond_thermodynamic_gauge_connection T n,
    bond_entropy_production T n]

/-- Entropy production has a well-defined direct-limit image along the tower. -/
theorem directLimit_entropy_production_compatible
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    ofStage T (n + 1) (entropy_production (T.tower.stage (n + 1)).flow) =
      ofStage T n (entropy_production (T.tower.stage n).flow) := by
  rw [← bond_entropy_production T n]
  exact ofStage_bond T n (entropy_production (T.tower.stage n).flow)

/-- Thermodynamic curvature has a well-defined direct-limit image along the tower. -/
theorem directLimit_thermodynamic_curvature_compatible
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    ofStage T (n + 1) (thermodynamic_curvature (T.tower.stage (n + 1)).flow) =
      ofStage T n (thermodynamic_curvature (T.tower.stage n).flow) := by
  rw [← bond_thermodynamic_curvature T n]
  exact ofStage_bond T n (thermodynamic_curvature (T.tower.stage n).flow)

/-- The existing finite entropy identity is available at every stage of the direct system. -/
theorem stage_entropy_identity
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    (T.tower.stage n).rn.entropy =
      (T.tower.stage n).rn.expectationBeta (T.tower.stage n).rn.modularPotential :=
  (T.tower.stage n).entropy_eq_expectation_modularPotential

/-- The existing finite curvature trace identity is available at every stage. -/
theorem stage_pathEntropy_curvature_identity
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    (T.tower.stage n).pathPacket.pathEntropy =
      (T.tower.stage n).pathPacket.trace
        (thermodynamic_curvature (T.tower.stage n).pathPacket.flow) :=
  (T.tower.stage n).pathPacket.pathEntropy_eq_curvatureTrace

/-- The direct-limit carrier is a genuine inhabited quotient type. -/
theorem directLimitCarrier_nonempty
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) :
    Nonempty (DirectLimitCarrier T) :=
  ⟨default⟩

/-- The thermodynamic gauge connection has a well-defined direct-limit image. -/
theorem directLimit_thermodynamic_gauge_connection_compatible
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    ofStage T (n + 1)
        (thermodynamic_gauge_connection (T.tower.stage (n + 1)).flow) =
      ofStage T n
        (thermodynamic_gauge_connection (T.tower.stage n).flow) := by
  rw [← bond_thermodynamic_gauge_connection T n]
  exact ofStage_bond T n (thermodynamic_gauge_connection (T.tower.stage n).flow)

/--
Inductive-limit lift theorem for the finite `FiniteMDPASJMStageData` tower.

The theorem exposes the concrete direct-limit carrier, its finite-stage maps,
the one-step bonding compatibility, and the finite operator identities that
survive as equalities in that carrier.  It does not assert analytic completion,
C*-closure, or transport of scalar Souriau identities by the operator bonding
maps.
-/
theorem inductiveLimitCarrier_lifts_finiteIdentities
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) :
    Nonempty (DirectLimitCarrier T) ∧
      ∃ ofStageMap : ∀ _n : ℕ, Op → DirectLimitCarrier T,
        (∀ n x, ofStageMap (n + 1) (T.bond n x) = ofStageMap n x) ∧
        (∀ n,
          ofStageMap (n + 1)
              (entropy_production (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (entropy_production (T.tower.stage n).flow)) ∧
        (∀ n,
          ofStageMap (n + 1)
              (thermodynamic_gauge_connection (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (thermodynamic_gauge_connection (T.tower.stage n).flow)) ∧
        (∀ n,
          ofStageMap (n + 1)
              (thermodynamic_curvature (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (thermodynamic_curvature (T.tower.stage n).flow)) ∧
        (∀ n,
          (T.tower.stage n).rn.entropy =
            (T.tower.stage n).rn.expectationBeta
              (T.tower.stage n).rn.modularPotential) ∧
        (∀ n,
          (T.tower.stage n).pathPacket.pathEntropy =
            (T.tower.stage n).pathPacket.trace
              (thermodynamic_curvature (T.tower.stage n).pathPacket.flow)) := by
  refine ⟨directLimitCarrier_nonempty T, (fun n x => ofStage T n x), ?_⟩
  exact ⟨
    ofStage_bond T,
    directLimit_entropy_production_compatible T,
    directLimit_thermodynamic_gauge_connection_compatible T,
    directLimit_thermodynamic_curvature_compatible T,
    stage_entropy_identity T,
    stage_pathEntropy_curvature_identity T⟩

end FiniteMDPASJMDirectSystem

end InfoGeometry.Physics.MDPASJMSouriauDigest
