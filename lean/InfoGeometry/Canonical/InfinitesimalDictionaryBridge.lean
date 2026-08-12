import Mathlib.Tactic
import InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
import InfoGeometry.Canonical.ArakiItakuraSaitoCollapse
import InfoGeometry.Canonical.ConnesRadonNikodymCocycle
import InfoGeometry.Canonical.MaximumCaliberKLSplit
import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Canonical.SouriauModularBregmanOperator
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Volume.ConnesInfinitesimal
import InfoGeometry.Volume.LogarithmicOrderParameterConnesBridge

/-!
# Infinitesimal Dictionary Bridge

Theorem-safe bridge connecting the classical logarithmic / Bregman / KL lane to
its operator-algebraic readouts:

* `log Q` / `d log Q` from the Amari--Souriau thermodynamic gauge interface;
* symmetric/antisymmetric KL splitting from `MaximumCaliberKLSplit`;
* Araki/Itakura--Saito collapse through explicit operator readouts; and
* Connes Radon--Nikodym cocycle derivative as modular-Hamiltonian difference.

This file does **not** prove the full Type III modular theory, global KMS
classification, or de Rham/cohomological emergence theorem. It records only the
exact readback pattern of those notions when explicit owner-side witnesses are
supplied.
-/

namespace InfoGeometry.Canonical.InfinitesimalDictionaryBridge

open InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
open InfoGeometry.Canonical.ArakiItakuraSaitoCollapse
open InfoGeometry.Canonical.MaximumCaliberKLSplit
open InfoGeometry.Canonical.SouriauModularBregmanOperator
open InfoGeometry.Topology.ThermodynamicGauge
open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Volume.ConnesInfinitesimal

/--
Explicit bridge data for the infinitesimal dictionary.

`pathConstraintScalar` is the scalar readout of the algebra-valued path
constraint/current.  This keeps the classical divergence lane and the
operator-valued thermodynamic lane honestly separated.
-/
structure InfinitesimalDictionaryPacket
    (Θ V State Op Alg X : Type*)
    [AddCommGroup V] [AddGroup Op] [Ring Alg] where
  logPartition : LogPartitionPotentialBridge Θ V
  gauge : SouriauAmariGauge Alg Θ V X
  divergence : State → State → ℝ
  toOperator : State → Op
  operatorPacket : NoncommutativeItakuraSaitoPacket Op
  pathConstraint : Alg
  pathReadout : Alg → ℝ
  pathConstraintScalar : ℝ
  pathConstraintScalar_eq_readout : pathConstraintScalar = pathReadout pathConstraint
  pathConstraint_eq_dlnQ : pathConstraint = gauge.flow.d_ln_Q
  entropy_commutator :
    gauge.flow.P_forward * gauge.flow.P_backward -
      gauge.flow.P_backward * gauge.flow.P_forward = pathConstraint
  /-- Infinitesimal generator of the Connes RN cocycle after choosing a readout lane. -/
  connesInfinitesimal : Alg
  /-- Modular-Hamiltonian difference `K_ψ - K_φ` in the same lane. -/
  modularHamiltonianDifference : Alg
  /-- Gradient of the Araki/Bregman relative entropy readout. -/
  arakiRelativeEntropyGradient : Alg
  /-- Self-concordant barrier force `-d log Q`. -/
  selfConcordantBarrierForce : Alg
  connes_eq_modular :
    connesInfinitesimal = modularHamiltonianDifference
  modular_eq_pathConstraint :
    modularHamiltonianDifference = pathConstraint
  arakiGradient_eq_neg_pathConstraint :
    arakiRelativeEntropyGradient = -pathConstraint
  barrierForce_eq_neg_pathConstraint :
    selfConcordantBarrierForce = -pathConstraint
  arakiCollapse : ∀ ω φ : State,
    restrictedAraki (fun s t => divergence s t) ω φ =
      operatorPacket.divergence (toOperator ω) (toOperator φ)

namespace InfinitesimalDictionaryPacket

variable {Θ V State Op Alg X : Type*}
variable [AddCommGroup V] [AddGroup Op] [Ring Alg]
variable (P : InfinitesimalDictionaryPacket Θ V State Op Alg X)

/--
Operator-valued variation of the state-surprisal generator.

With `K = -log Q`, its infinitesimal variation is `dK = -d log Q`.  This is
derived from the unique path-current owner and is not Boltzmann macroentropy.
-/
def stateSurprisalVariation : Alg :=
  -P.pathConstraint

/-- The logarithmic partition potential is explicitly `log Q`. -/
theorem psi_eq_logQ (θ : Θ) :
    P.logPartition.info.Ψ θ = Real.log (P.logPartition.Q θ) :=
  P.logPartition.psi_eq_logQ θ

/-- The classical Bregman divergence vanishes on the diagonal. -/
theorem bregman_self (θ : Θ) :
    P.logPartition.info.bregman θ θ = 0 :=
  P.logPartition.info.bregman_self θ

/-- The thermodynamic force is the de Rham logarithmic current `d log Q`. -/
theorem pathConstraint_eq_dlnQ_readout :
    P.pathConstraint = P.gauge.flow.d_ln_Q :=
  P.pathConstraint_eq_dlnQ

/-- Entropy production is identified with `d log Q` through the supplied commutator bridge. -/
theorem entropy_production_eq_dlnQ :
    entropy_production P.gauge.flow = P.gauge.flow.d_ln_Q := by
  exact de_rham_potential_equals_entropy_production_of_commutator
    (flow := P.gauge.flow)
    (P.entropy_commutator.trans P.pathConstraint_eq_dlnQ)

/-- The scalar current readout is the readout of `d log Q`. -/
theorem pathConstraintScalar_eq_dlnQ_readout :
    P.pathConstraintScalar = P.pathReadout P.gauge.flow.d_ln_Q := by
  rw [P.pathConstraintScalar_eq_readout, P.pathConstraint_eq_dlnQ]

/-- The Connes RN infinitesimal is the modular-Hamiltonian difference. -/
theorem connesInfinitesimal_eq_modularHamiltonianDifference :
    P.connesInfinitesimal = P.modularHamiltonianDifference :=
  P.connes_eq_modular

/-- The modular-Hamiltonian difference is the logarithmic de Rham current. -/
theorem modularHamiltonianDifference_eq_dlnQ :
    P.modularHamiltonianDifference = P.gauge.flow.d_ln_Q := by
  rw [P.modular_eq_pathConstraint, P.pathConstraint_eq_dlnQ]

/-- The Connes RN infinitesimal is the logarithmic de Rham current. -/
theorem connesInfinitesimal_eq_dlnQ :
    P.connesInfinitesimal = P.gauge.flow.d_ln_Q := by
  rw [P.connes_eq_modular, P.modularHamiltonianDifference_eq_dlnQ]

/-- The Connes RN infinitesimal is the entropy-production commutator. -/
theorem connesInfinitesimal_eq_entropyProduction :
    P.connesInfinitesimal = entropy_production P.gauge.flow := by
  rw [P.connesInfinitesimal_eq_dlnQ, ← P.entropy_production_eq_dlnQ]

/-- The state-surprisal variation is the negative logarithmic de Rham current. -/
theorem stateSurprisalVariation_eq_neg_dlnQ :
    P.stateSurprisalVariation = -P.gauge.flow.d_ln_Q := by
  rw [stateSurprisalVariation, P.pathConstraint_eq_dlnQ]

/-- The state-surprisal variation is `dK = -d log Q`. -/
theorem stateSurprisalVariation_eq_neg_logGeneratorVariation :
    P.stateSurprisalVariation = -P.gauge.flow.d_ln_Q :=
  P.stateSurprisalVariation_eq_neg_dlnQ

/-- The Araki/Bregman gradient is the negative logarithmic de Rham current. -/
theorem arakiRelativeEntropyGradient_eq_neg_dlnQ :
    P.arakiRelativeEntropyGradient = -P.gauge.flow.d_ln_Q := by
  rw [P.arakiGradient_eq_neg_pathConstraint, P.pathConstraint_eq_dlnQ]

/-- The self-concordant barrier force is the negative logarithmic de Rham current. -/
theorem selfConcordantBarrierForce_eq_neg_dlnQ :
    P.selfConcordantBarrierForce = -P.gauge.flow.d_ln_Q := by
  rw [P.barrierForce_eq_neg_pathConstraint, P.pathConstraint_eq_dlnQ]

/-- The Araki/Bregman gradient and self-concordant barrier force are the same readout. -/
theorem arakiRelativeEntropyGradient_eq_barrierForce :
    P.arakiRelativeEntropyGradient = P.selfConcordantBarrierForce := by
  rw [P.arakiRelativeEntropyGradient_eq_neg_dlnQ, P.selfConcordantBarrierForce_eq_neg_dlnQ]

/-- Barrier force is the negative of the Connes RN infinitesimal. -/
theorem selfConcordantBarrierForce_eq_neg_connesInfinitesimal :
    P.selfConcordantBarrierForce = -P.connesInfinitesimal := by
  rw [P.selfConcordantBarrierForce_eq_neg_dlnQ, P.connesInfinitesimal_eq_dlnQ]

/--
At exact detailed balance, the de Rham current, Connes infinitesimal, modular
Hamiltonian difference, state-surprisal variation, Araki gradient, and barrier
force all vanish.
-/
theorem detailedBalance_trivializes_infinitesimal_dictionary
    (hdb : entropy_production P.gauge.flow = 0) :
    P.gauge.flow.d_ln_Q = 0 ∧
    P.connesInfinitesimal = 0 ∧
    P.modularHamiltonianDifference = 0 ∧
    P.stateSurprisalVariation = 0 ∧
    P.arakiRelativeEntropyGradient = 0 ∧
    P.selfConcordantBarrierForce = 0 := by
  have hdln : P.gauge.flow.d_ln_Q = 0 := by
    rw [← P.entropy_production_eq_dlnQ]
    exact hdb
  have hpath : P.pathConstraint = 0 := by
    rw [P.pathConstraint_eq_dlnQ, hdln]
  refine ⟨hdln, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P.connes_eq_modular, P.modular_eq_pathConstraint, hpath]
  · rw [P.modular_eq_pathConstraint, hpath]
  · simp [stateSurprisalVariation, hpath]
  · rw [P.arakiGradient_eq_neg_pathConstraint, hpath, neg_zero]
  · rw [P.barrierForce_eq_neg_pathConstraint, hpath, neg_zero]

/-- The operatorial Araki readout collapses to the noncommutative Itakura--Saito packet. -/
theorem restrictedAraki_eq_operatorPacket
    (ω φ : State) :
    restrictedAraki (fun s t => P.divergence s t) ω φ =
      P.operatorPacket.divergence (P.toOperator ω) (P.toOperator φ) :=
  P.arakiCollapse ω φ

/-- The directed divergence splits into symmetric and antisymmetric pieces. -/
theorem divergence_eq_symmetric_add_antisymmetric
    (ω φ : State) :
    P.divergence ω φ =
      symmetricDivergence P.divergence ω φ +
        antisymmetricDivergence P.divergence ω φ :=
  MaximumCaliberKLSplit.divergence_eq_symmetric_add_antisymmetric P.divergence ω φ

/-- The symmetric component is the Jeffreys/half-sum divergence. -/
theorem symmetric_eq_jeffreys
    (ω φ : State) :
    jeffreysDivergence P.divergence ω φ = symmetricDivergence P.divergence ω φ :=
  MaximumCaliberKLSplit.jeffreysDivergence_eq_symmetricDivergence P.divergence ω φ

/-- The antisymmetric component changes sign under swapping the two states. -/
theorem antisymmetric_swap
    (ω φ : State) :
    antisymmetricDivergence P.divergence φ ω = -antisymmetricDivergence P.divergence ω φ :=
  MaximumCaliberKLSplit.antisymmetricDivergence_swap P.divergence ω φ

/-- A supplied scalar calibration ties the antisymmetric divergence to the scalar current readout. -/
theorem antisymmetric_eq_pathConstraintScalar_of_calibration
    (ω φ : State)
    (hcal : antisymmetricDivergence P.divergence ω φ = P.pathConstraintScalar) :
    antisymmetricDivergence P.divergence ω φ = P.pathConstraintScalar :=
  hcal

end InfinitesimalDictionaryPacket

/-! ## Connes RN derivative owner readbacks -/

section CoadjointConnes

variable (H1 H2 : InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry.Operator)
variable (beta1 μ1 μχ1 beta2 μ2 μχ2 : ℝ)
variable (flow : CausalNonequilibriumFlow InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry.Operator)

/-- The Connes cocycle derivative is definitionally the modular-Hamiltonian difference. -/
theorem coadjoint_cocycleDerivative_eq_modularHamiltonianDifference :
    ConnesCocycle.connesRadonNikodymDerivative H1 H2 beta1 μ1 μχ1 beta2 μ2 μχ2 =
      InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry.grandCanonicalModularGenerator H2 beta2 μ2 μχ2 -
      InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry.grandCanonicalModularGenerator H1 beta1 μ1 μχ1 :=
  rfl

/-- If the modular-Hamiltonian difference is calibrated to `d log Q`, so is the RN infinitesimal. -/
theorem coadjoint_cocycleDerivative_eq_dlnQ_of_modularDifference
    (hmod : InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry.grandCanonicalModularGenerator H2 beta2 μ2 μχ2 -
      InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry.grandCanonicalModularGenerator H1 beta1 μ1 μχ1 = flow.d_ln_Q) :
    ConnesCocycle.connesRadonNikodymDerivative H1 H2 beta1 μ1 μχ1 beta2 μ2 μχ2 =
      flow.d_ln_Q := by
  rw [coadjoint_cocycleDerivative_eq_modularHamiltonianDifference H1 H2 beta1 μ1 μχ1 beta2 μ2 μχ2]
  exact hmod

/-- If the modular-Hamiltonian difference is calibrated to entropy production, so is the RN infinitesimal. -/
theorem coadjoint_cocycleDerivative_eq_entropyProduction_of_modularDifference
    (hmod : InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry.grandCanonicalModularGenerator H2 beta2 μ2 μχ2 -
      InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry.grandCanonicalModularGenerator H1 beta1 μ1 μχ1 = flow.d_ln_Q)
    (hentropy : entropy_production flow = flow.d_ln_Q) :
    ConnesCocycle.connesRadonNikodymDerivative H1 H2 beta1 μ1 μχ1 beta2 μ2 μχ2 =
      entropy_production flow := by
  rw [coadjoint_cocycleDerivative_eq_dlnQ_of_modularDifference
    H1 H2 beta1 μ1 μχ1 beta2 μ2 μχ2 flow hmod, ← hentropy]

end CoadjointConnes

/-! ## Scalar Connes modular-Hamiltonian shadow -/

section ScalarConnesShadow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Scalar Connes modular Hamiltonian is the negative cocycle log-potential. -/
theorem connesScalarModularHamiltonian_eq_neg_cocycleLogPotential
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (B : ScalarCocycleBridge (H := H) σ)
    (t : ℝ) :
    InfoGeometry.Volume.LogarithmicOrderParameterConnesBridge.connesScalarModularHamiltonian
        (H := H) σ u B t =
      -cocycleLogPotential (H := H) σ u B t :=
  rfl

/--
Concrete scalar Radon--Nikodym readout: along the positive exponential density
path `exp(rate * t)`, the logarithmic RN derivative is exactly the modular
Hamiltonian difference/rate.
-/
theorem scalarRNLogDerivative_eq_modularHamiltonianDifference
    (rate t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => unitsRNBridge.rn (expUnitsPath rate τ))
      rate t :=
  unitsRNBridge_rn_expUnitsPath_hasDerivAt rate t

/--
At the infinitesimal base point, the scalar RN cocycle derivative is the
modular-Hamiltonian difference/rate.
-/
theorem scalarRNLogDerivative_at_zero_eq_modularHamiltonianDifference
    (rate : ℝ) :
    HasDerivAt
      (fun τ : ℝ => unitsRNBridge.rn (expUnitsPath rate τ))
      rate 0 :=
  scalarRNLogDerivative_eq_modularHamiltonianDifference (rate := rate) 0

end ScalarConnesShadow

/-! ## Finite `Δ`-primary modular-Hamiltonian owner readback -/

section FiniteDeltaPrimary

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.Canonical.RelativeModularOperator

variable {n : ℕ} [Nonempty (Fin n)]

/-- In the finite commuting lane, state surprisal is `K = -log Δ` componentwise. -/
theorem finite_stateSurprisal_eq_neg_log_delta_diag
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeModularHamiltonianOperator (n := n) q q0 i i =
      -Real.log (relativeModularOperator (n := n) q q0 i i) := by
  rw [relativeModularHamiltonianOperator_diag]
  exact relativeModularPotential_eq_neg_log_relativeModularOperator_diag (n := n) q q0 i

end FiniteDeltaPrimary

end InfoGeometry.Canonical.InfinitesimalDictionaryBridge
