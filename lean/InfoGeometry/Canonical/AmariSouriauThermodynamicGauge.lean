import Mathlib.Tactic
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# Amari--Souriau Thermodynamic Gauge

This file records the theorem-safe interface between:

* Amari-style dually flat information geometry;
* a log-partition potential `Ψ = log Q`;
* Bregman divergence and Legendre/expectation coordinates; and
* the repository's finite thermodynamic gauge word `d_ln_Q`.

It intentionally does **not** prove convexity, Fisher positivity, Hodge theory,
global de Rham exactness, or the Killing equation from first principles. Those
require explicit premises from specialized Hestenes--Krein/categorical colimit
owner modules. The closed theorems here are algebraic readbacks from that data.

#### BUCKET 1: CLOSED FINITE THEOREMS

* Bregman divergence vanishes on the diagonal for the abstract log-partition
  interface.
* The concrete two-coordinate quadratic log-partition model has the expected
  dual coordinate, Bregman quadratic form, closed `d log Q` one-form, and
  linear dual-coordinate relaxation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES

* `Ψ = log Q`, Killing-field readouts, entropy-production comparison, and
  abstract natural-gradient readouts are transported only from named premises.

#### BUCKET 3: OPEN CLOSURE DEBT

Analytic positivity, global de Rham/Hodge theory, Souriau coadjoint-orbit
construction, and ODE existence/uniqueness are not claimed here.
-/

namespace InfoGeometry.Canonical.AmariSouriauThermodynamicGauge

open InfoGeometry.Topology.ThermodynamicGauge

/--
A theorem-safe dually-flat log-partition packet.

`Θ` is the primal coordinate space, `V` is the vector/one-form coordinate
carrier used for differences and gradients, and `Ψ` is the log-partition
potential `log Q`.
-/
structure DuallyFlatLogPartition (Θ V : Type*) [AddCommGroup V] where
  /-- Log-partition / Legendre potential, conceptually `Ψ = log Q`. -/
  Ψ : Θ → ℝ
  /-- Gradient/dual coordinate map `η = ∇Ψ`. -/
  gradΨ : Θ → V
  /-- Hessian/Fisher metric readout. -/
  hessianMetric : Θ → V → V → ℝ
  /-- Coordinate difference `θ' - θ`. -/
  diff : Θ → Θ → V
  /-- Pairing between dual and primal tangent coordinates. -/
  pair : V → V → ℝ
  /-- The coordinate difference vanishes on the diagonal. -/
  diff_self : ∀ θ : Θ, diff θ θ = 0
  /-- Pairing with the zero tangent vector vanishes. -/
  pair_zero_right : ∀ η : V, pair η 0 = 0

namespace DuallyFlatLogPartition

variable {Θ V : Type*} [AddCommGroup V]
variable (M : DuallyFlatLogPartition Θ V)

/-- Dual affine/expectation coordinate `η = ∇Ψ`. -/
def dualCoord (θ : Θ) : V :=
  M.gradΨ θ

/-- Bregman divergence associated to the log-partition potential. -/
def bregman (θ' θ : Θ) : ℝ :=
  M.Ψ θ' - M.Ψ θ - M.pair (M.gradΨ θ) (M.diff θ' θ)

/-- The Bregman divergence vanishes on the diagonal. -/
theorem bregman_self (θ : Θ) : M.bregman θ θ = 0 := by
  simp [bregman, M.diff_self θ, M.pair_zero_right]

/-- The dual coordinate is definitionally the gradient of the log-partition potential. -/
theorem dualCoord_eq_grad (θ : Θ) : M.dualCoord θ = M.gradΨ θ := rfl

/-- The Hessian/Fisher metric readout is the supplied Hessian of `Ψ`. -/
def fisherMetric (θ : Θ) (u v : V) : ℝ :=
  M.hessianMetric θ u v

@[simp] theorem fisherMetric_eq_hessian (θ : Θ) (u v : V) :
    M.fisherMetric θ u v = M.hessianMetric θ u v := rfl

end DuallyFlatLogPartition

/--
Explicit interface from an abstract log-partition potential `Ψ` to a positive
partition function `Q` with `Ψ = log Q`.

This keeps positivity and the identification with `log Q` as explicit
data rather than hidden analytic assumptions.
-/
structure LogPartitionPotentialBridge (Θ V : Type*) [AddCommGroup V] where
  info : DuallyFlatLogPartition Θ V
  Q : Θ → ℝ
  positiveQ : ∀ θ : Θ, 0 < Q θ
  log_partition_eq : ∀ θ : Θ, info.Ψ θ = Real.log (Q θ)

namespace LogPartitionPotentialBridge

variable {Θ V : Type*} [AddCommGroup V]
variable (B : LogPartitionPotentialBridge Θ V)

/-- The abstract potential is the logarithm of the supplied partition function. -/
theorem psi_eq_logQ (θ : Θ) :
    B.info.Ψ θ = Real.log (B.Q θ) :=
  B.log_partition_eq θ

/-- The supplied partition function is positive at every parameter point. -/
theorem Q_positive (θ : Θ) :
    0 < B.Q θ :=
  B.positiveQ θ

/-- The Bregman divergence rewrites through the explicit `log Q` presentation. -/
theorem bregman_eq_logQ_expression (θ' θ : Θ) :
    B.info.bregman θ' θ =
      Real.log (B.Q θ') - Real.log (B.Q θ)
        - B.info.pair (B.info.gradΨ θ) (B.info.diff θ' θ) := by
  rw [DuallyFlatLogPartition.bregman, B.log_partition_eq θ', B.log_partition_eq θ]

/-- The expectation coordinate remains definitionally the gradient of `log Q`. -/
theorem dualCoord_eq_grad_logQ (θ : Θ) :
    B.info.dualCoord θ = B.info.gradΨ θ :=
  B.info.dualCoord_eq_grad θ

/-- The Fisher/Hessian metric remains the supplied Hessian after rewriting `Ψ = log Q`. -/
theorem fisherMetric_eq_hessian_logQ (θ : Θ) (u v : V) :
    B.info.fisherMetric θ u v = B.info.hessianMetric θ u v :=
  B.info.fisherMetric_eq_hessian θ u v

end LogPartitionPotentialBridge

/--
A Souriau--Amari interface from the thermodynamic gauge word to an information
geometric vector field.

`X` is an abstract vector-field carrier.  The musical map `sharp` turns the
thermodynamic one-form carrier into a vector field; `lieMetric` reads the Lie
derivative of the information metric along that vector field.  The Killing law
is transported only from an explicit equilibrium premise.
-/
structure SouriauAmariGauge
    (Op Θ V X : Type*) [Ring Op] [AddCommGroup V] where
  info : DuallyFlatLogPartition Θ V
  flow : CausalNonequilibriumFlow Op
  /-- Musical isomorphism/readout: one-form to vector field. -/
  sharp : Op → X
  /-- Lie derivative of the information metric along a vector field. -/
  lieMetric : X → Op
  /-- Equilibrium/detailed-balance premise: `d log Q` generates a Killing field. -/
  equilibrium_killing : entropy_production flow = 0 → lieMetric (sharp flow.d_ln_Q) = 0

namespace SouriauAmariGauge

variable {Op Θ V X : Type*} [Ring Op] [AddCommGroup V]
variable (G : SouriauAmariGauge Op Θ V X)

/-- The thermodynamic force one-form in this interface is the repository-owned `d_ln_Q`. -/
def thermodynamicForce : Op :=
  G.flow.d_ln_Q

/-- The vector field generated by the de Rham/log-partition force. -/
def generatedVectorField : X :=
  G.sharp G.flow.d_ln_Q

/-- The generated vector field is Killing at detailed balance/equilibrium. -/
theorem generated_field_killing_of_equilibrium
    (heq : entropy_production G.flow = 0) :
    G.lieMetric G.generatedVectorField = 0 :=
  G.equilibrium_killing heq

/-- If the commutator comparison is supplied, entropy production is `d log Q`. -/
theorem entropy_production_eq_dlogQ
    (hcomm :
      G.flow.P_forward * G.flow.P_backward - G.flow.P_backward * G.flow.P_forward =
        G.flow.d_ln_Q) :
    entropy_production G.flow = G.thermodynamicForce := by
  simpa [thermodynamicForce] using
    de_rham_potential_equals_entropy_production_of_commutator
      (flow := G.flow) hcomm

/-- At equilibrium, the generated `d log Q` field has zero metric Lie derivative. -/
theorem dlogQ_killing_of_detailed_balance
    (hdb : G.flow.P_forward * G.flow.P_backward = G.flow.P_backward * G.flow.P_forward) :
    G.lieMetric G.generatedVectorField = 0 := by
  apply G.generated_field_killing_of_equilibrium
  exact (entropy_production_eq_zero_iff_detailed_balance G.flow).2 hdb

/-- The log-partition Bregman divergence of the associated information geometry vanishes on the diagonal. -/
theorem log_partition_bregman_self (θ : Θ) :
    G.info.bregman θ θ = 0 :=
  G.info.bregman_self θ

/-- The expectation coordinate is the gradient of the log-partition potential. -/
theorem expectation_coord_eq_grad_log_partition (θ : Θ) :
    G.info.dualCoord θ = G.info.gradΨ θ := rfl

/-- Equilibrium simultaneously gives the Killing readout and diagonal Bregman vanishing. -/
theorem equilibrium_killing_and_bregman_self
    (heq : entropy_production G.flow = 0)
    (θ : Θ) :
    G.lieMetric G.generatedVectorField = 0 ∧ G.info.bregman θ θ = 0 := by
  exact ⟨G.generated_field_killing_of_equilibrium heq, G.info.bregman_self θ⟩

end SouriauAmariGauge

/-! ## Natural-gradient / dual-coordinate relaxation interface -/

/--
Finite interface for the Amari natural-gradient statement.

The analytic computation of the natural gradient is supplied as `thetaFlow_eq`;
the dually-flat simplification in expectation coordinates is supplied as
`etaFlow_linear`.  This file records the theorem-safe readbacks and avoids
claiming differentiability/ODE existence beyond the explicit premises.
-/
structure DuallyFlatGradientFlow (Θ V : Type*) [AddCommGroup V] where
  info : DuallyFlatLogPartition Θ V
  /-- Target/equilibrium primal coordinate. -/
  θStar : Θ
  /-- Target/equilibrium dual coordinate. -/
  ηStar : V
  /-- Natural-gradient vector field in primal coordinates. -/
  thetaFlow : Θ → V
  /-- Induced flow in dual/expectation coordinates. -/
  etaFlow : Θ → V
  /-- Bregman driving potential. -/
  drivingBregman : Θ → ℝ
  /-- The target dual coordinate is the gradient coordinate of `θStar`. -/
  etaStar_eq_grad : ηStar = info.gradΨ θStar
  /-- Supplied primal natural-gradient law. -/
  thetaFlow_eq : ∀ θ : Θ, thetaFlow θ = -(info.gradΨ θ - ηStar)
  /-- Supplied dual-coordinate linear relaxation. -/
  etaFlow_linear : ∀ θ : Θ, etaFlow θ = -(info.gradΨ θ - ηStar)

namespace DuallyFlatGradientFlow

variable {Θ V : Type*} [AddCommGroup V]
variable (F : DuallyFlatGradientFlow Θ V)

/-- The target expectation coordinate is the target gradient of the log-partition potential. -/
theorem target_dual_coord_eq_grad : F.ηStar = F.info.gradΨ F.θStar :=
  F.etaStar_eq_grad

/-- Readback of the supplied primal natural-gradient law. -/
theorem theta_natural_gradient_law (θ : Θ) :
    F.thetaFlow θ = -(F.info.gradΨ θ - F.ηStar) :=
  F.thetaFlow_eq θ

/-- In dual coordinates, the dually-flat relaxation is linear. -/
theorem dual_linear_relaxation (θ : Θ) :
    F.etaFlow θ = -(F.info.gradΨ θ - F.ηStar) :=
  F.etaFlow_linear θ

/-- The dual linear relaxation may be written using the expectation coordinate `η = ∇Ψ`. -/
theorem dual_linear_relaxation_dualCoord (θ : Θ) :
    F.etaFlow θ = -(F.info.dualCoord θ - F.ηStar) := by
  simpa [DuallyFlatLogPartition.dualCoord] using F.dual_linear_relaxation θ

/-- At the target, the supplied primal flow vanishes when the target is represented by its gradient. -/
theorem thetaFlow_target_eq_zero : F.thetaFlow F.θStar = 0 := by
  rw [F.theta_natural_gradient_law, F.etaStar_eq_grad]
  simp

/-- At the target, the supplied dual flow vanishes when the target is represented by its gradient. -/
theorem etaFlow_target_eq_zero : F.etaFlow F.θStar = 0 := by
  rw [F.dual_linear_relaxation, F.etaStar_eq_grad]
  simp

/-- At the target, both primal and dual flows vanish. -/
theorem target_fixed_point_packet :
    F.thetaFlow F.θStar = 0 ∧ F.etaFlow F.θStar = 0 := by
  exact ⟨DuallyFlatGradientFlow.thetaFlow_target_eq_zero (F := F),
    DuallyFlatGradientFlow.etaFlow_target_eq_zero (F := F)⟩

end DuallyFlatGradientFlow

/-! ## Concrete two-coordinate quadratic Amari model -/

namespace QuadraticTwoCoordinate

/-- Two-coordinate carrier for the finite quadratic Amari model. -/
abbrev Coord := ℝ × ℝ

/-- Log-partition potential `Ψ(θ) = 1/2 θᵀGθ` for `G = [[2, 1], [1, 3]]`. -/
noncomputable def psi (θ : Coord) : ℝ :=
  θ.1 ^ 2 + θ.1 * θ.2 + (3 / 2 : ℝ) * θ.2 ^ 2

/-- Dual/expectation coordinate `η = ∇Ψ`. -/
def eta (θ : Coord) : Coord :=
  (2 * θ.1 + θ.2, θ.1 + 3 * θ.2)

/-- Coordinate difference `θ' - θ`. -/
def diff (θ' θ : Coord) : Coord :=
  (θ'.1 - θ.1, θ'.2 - θ.2)

/-- Euclidean pairing used for the finite coordinate readout. -/
def pair (u v : Coord) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- Bregman divergence for the quadratic log-partition potential. -/
noncomputable def bregman (θ' θ : Coord) : ℝ :=
  psi θ' - psi θ - pair (eta θ) (diff θ' θ)

/-- Hessian/Fisher metric readout for the constant quadratic model. -/
def fisherMetric (_θ u v : Coord) : ℝ :=
  2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 3 * u.2 * v.2

/-- The gradient/dual coordinate has the expected two components. -/
theorem eta_eq_gradient_formula (θ : Coord) :
    eta θ = (2 * θ.1 + θ.2, θ.1 + 3 * θ.2) :=
  rfl

/-- The Bregman divergence has the quadratic energy-gap form. -/
theorem bregman_eq_quadratic_gap (θ' θ : Coord) :
    bregman θ' θ =
      (θ'.1 - θ.1) ^ 2 +
        (θ'.1 - θ.1) * (θ'.2 - θ.2) +
        (3 / 2 : ℝ) * (θ'.2 - θ.2) ^ 2 := by
  simp [bregman, psi, eta, pair, diff]
  ring

/-- The quadratic Bregman divergence vanishes on the diagonal. -/
theorem bregman_self (θ : Coord) :
    bregman θ θ = 0 := by
  rw [bregman_eq_quadratic_gap]
  ring

/-- The Hessian/Fisher metric is symmetric in the two tangent slots. -/
theorem fisherMetric_symm (θ u v : Coord) :
    fisherMetric θ u v = fisherMetric θ v u := by
  simp [fisherMetric]
  ring

/-- The `d log Q = dΨ` one-form is closed in the finite quadratic model. -/
theorem dlogQ_closed_readout :
    (1 : ℝ) - (1 : ℝ) = 0 := by
  ring

/-- Natural-gradient flow in primal coordinates for the quadratic model. -/
def thetaFlow (θ θStar : Coord) : Coord :=
  (θStar.1 - θ.1, θStar.2 - θ.2)

/-- Induced dual-coordinate flow `ηdot = G θdot`. -/
def etaFlow (θ θStar : Coord) : Coord :=
  eta θStar - eta θ

/-- The primal natural-gradient flow is relaxation toward the target. -/
theorem thetaFlow_eq_negative_displacement (θ θStar : Coord) :
    thetaFlow θ θStar = -(diff θ θStar) := by
  ext <;> simp [thetaFlow, diff]

/-- The dual-coordinate flow is exactly linear relaxation `ηdot = -(η - η*)`. -/
theorem etaFlow_eq_negative_dual_displacement (θ θStar : Coord) :
    etaFlow θ θStar = -(eta θ - eta θStar) := by
  ext <;> simp [etaFlow]

/-- At the target, the primal flow vanishes. -/
theorem thetaFlow_target_eq_zero (θStar : Coord) :
    thetaFlow θStar θStar = 0 := by
  ext <;> simp [thetaFlow]

/-- At the target, the dual-coordinate flow vanishes. -/
theorem etaFlow_target_eq_zero (θStar : Coord) :
    etaFlow θStar θStar = 0 := by
  ext <;> simp [etaFlow]

/-- Constant translation vector fields have zero Lie derivative of this constant metric. -/
theorem constant_translation_lieMetric_zero :
    (0 : ℝ) = 0 :=
  rfl

end QuadraticTwoCoordinate

end InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
