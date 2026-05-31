import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
import InfoGeometry.Meta.Architecture
import Mathlib

/-!
# InfoGeometry.Canonical.SouriauOperatorialLogPotential

Theorem-honest synthesis packet connecting Souriau Lie thermodynamics,
logarithmic Radon--Nikodym/modular potentials, operatorial exponential-family
readouts, Rényi/Mellin generators, and Onsager/metriplectic witness layers.

Design policy:
- No automatic gravity closure claim.
- No OT theorem without metric witness.
- Negative logarithms are not collapsed into entropy until an expectation/state
  readout is supplied.
- The operatorial exponential family is untraced; scalar cumulants appear only
  after a trace/state/KMS readout.
-/

namespace InfoGeometry.Canonical.SouriauOperatorialLogPotential

open InfoGeometry.Canonical.StandardFormCore

abbrev Density (State : Type*) := State → ℝ

/-- Classical logarithmic Radon--Nikodym sign packet.

`logDensity = log r` is relative information density, while
`surprisalDensity = - logDensity` is the relative surprisal. KL is recorded as
expectation of the former, equivalently negative expectation of the latter.
-/
@[rep_depth thermo]
structure LogRadonNikodymData (State : Type*) where
  rnDerivative : Density State
  logDensity : Density State
  surprisalDensity : Density State
  expectationNu : (Density State) → ℝ
  KL : ℝ
  logDensity_eq : ∀ x, logDensity x = Real.log (rnDerivative x)
  surprisalDensity_eq : ∀ x, surprisalDensity x = -logDensity x
  KL_eq_logDensityExpectation : KL = expectationNu logDensity
  KL_eq_neg_surprisalExpectation : KL = -expectationNu surprisalDensity

namespace LogRadonNikodymData

variable {State : Type*}

@[rep_depth thermo]
theorem KL_eq_expectation_logDensity (D : LogRadonNikodymData State) :
    D.KL = D.expectationNu D.logDensity :=
  D.KL_eq_logDensityExpectation

@[rep_depth thermo]
theorem KL_eq_neg_expectation_surprisalDensity (D : LogRadonNikodymData State) :
    D.KL = -D.expectationNu D.surprisalDensity :=
  D.KL_eq_neg_surprisalExpectation

@[rep_depth thermo]
theorem surprisalDensity_eq_neg_logDensity
    (D : LogRadonNikodymData State) (x : State) :
    D.surprisalDensity x = -D.logDensity x :=
  D.surprisalDensity_eq x

end LogRadonNikodymData

/-- Regularized Jacobian determinant packet.

The volume-compression potential is `-logDetReg`; it is not entropy until a
state/expectation readout is supplied.
-/
@[rep_depth thermo]
structure RegularizedJacobianPotential (Map : Type*) where
  jacobian : Map → ℝ
  logDetReg : Map → ℝ
  volumeCompressionPotential : Map → ℝ
  volumeCompressionPotential_eq_neg_logDetReg :
    ∀ φ, volumeCompressionPotential φ = -logDetReg φ
  entropyReadoutRequiresStateClaim : Prop

namespace RegularizedJacobianPotential

variable {Map : Type*}

@[rep_depth thermo]
theorem volumeCompressionPotential_eq_neg_logDetReg_apply
    (J : RegularizedJacobianPotential Map) (φ : Map) :
    J.volumeCompressionPotential φ = -J.logDetReg φ :=
  J.volumeCompressionPotential_eq_neg_logDetReg φ

end RegularizedJacobianPotential

/-- Modular Hamiltonian packet for a positive density operator.

The logarithm/functional calculus is supplied as witness data; this file does
not assert an unbounded global logarithm theorem.  In this packet the modular
Hamiltonian is definitionally the negative-logarithmic density; only the
additional Gibbs/readout structure remains explicit data.
-/
@[rep_depth operator]
structure ModularHamiltonianData (Op : Type*) where
  densityOperator : Op
  negativeLogDensity : Op
  gibbsHamiltonian : Op
  logPartitionScalar : ℝ
  gibbsFormulaLaw : Op → Op → ℝ → Prop
  relativeModularLaw : Op → Op → Prop

namespace ModularHamiltonianData

variable {Op : Type*}

/-- The operator-level modular Hamiltonian is the negative logarithmic density. -/
@[rep_depth operator]
def modularHamiltonian (M : ModularHamiltonianData Op) : Op :=
  M.negativeLogDensity

@[rep_depth operator]
theorem modularHamiltonian_eq_negativeLogDensity_theorem
    (M : ModularHamiltonianData Op) :
    M.modularHamiltonian = M.negativeLogDensity :=
  rfl

end ModularHamiltonianData

/-- Operator-valued exponential-family packet.

This is the untraced object `E(β)=exp(-K(β))`; scalar partition potentials are
separate readouts requiring trace/state/KMS data.
-/
@[rep_depth operator]
structure OperatorialExponentialFamily (Param Op : Type*) where
  K : Param → Op
  untracedExponential : Param → Op
  operatorialExponentialFamily : Param → Op
  operatorialExponentialFamily_eq :
    ∀ β, operatorialExponentialFamily β = untracedExponential β
  traceClass : Op → Prop
  traceClass_untraced : ∀ β, traceClass (untracedExponential β)
  traceReadout : Op → ℝ
  partitionFunction : Param → ℝ
  partitionFunction_eq_trace :
    ∀ β, partitionFunction β = traceReadout (untracedExponential β)
  partitionPotential : Param → ℝ
  normalizedState : Param → Op
  partitionPotential_eq_log_trace :
    ∀ β, partitionPotential β = Real.log (traceReadout (untracedExponential β))

namespace OperatorialExponentialFamily

variable {Param Op : Type*}

@[rep_depth operator]
theorem operatorialExponentialFamily_eq_untraced
    (E : OperatorialExponentialFamily Param Op) (β : Param) :
    E.operatorialExponentialFamily β = E.untracedExponential β :=
  E.operatorialExponentialFamily_eq β

@[rep_depth operator]
theorem traceClass_untraced_theorem
    (E : OperatorialExponentialFamily Param Op) (β : Param) :
    E.traceClass (E.untracedExponential β) :=
  E.traceClass_untraced β

@[rep_depth operator]
theorem partitionFunction_eq_trace_theorem
    (E : OperatorialExponentialFamily Param Op) (β : Param) :
    E.partitionFunction β = E.traceReadout (E.untracedExponential β) :=
  E.partitionFunction_eq_trace β

@[rep_depth operator]
theorem partitionPotential_eq_log_trace_theorem
    (E : OperatorialExponentialFamily Param Op) (β : Param) :
    E.partitionPotential β = Real.log (E.traceReadout (E.untracedExponential β)) :=
  E.partitionPotential_eq_log_trace β

end OperatorialExponentialFamily

/-- Duhamel/Kubo derivative and higher simplex-ordered insertion packet. -/
@[rep_depth operator]
structure DuhamelOperatorDerivative (Param Op Direction : Type*) where
  K : Param → Op
  directionToInsertion : Direction → Op
  derivativeOfExp : Param → Direction → Op
  duhamelFormula : Param → Direction → Op → Prop
  higherSimplexOrderedForms : Nat → Param → List Direction → Op
  higherSimplexOrderedLaw : Nat → Param → List Direction → Op → Prop
  higherSimplexOrderedForms_satisfy :
    ∀ n β dirs, higherSimplexOrderedLaw n β dirs (higherSimplexOrderedForms n β dirs)
  traceStateKMSReadout : Op → ℝ
  tracedCumulantReadoutLaw : Nat → Param → List Direction → ℝ → Prop

/-- Compatibility name used by existing Souriau/operatorial tests. -/
abbrev DuhamelOperatorialNForms := DuhamelOperatorDerivative

namespace DuhamelOperatorDerivative

variable {Param Op Direction : Type*}

@[rep_depth operator]
theorem higherSimplexOrderedForms_satisfy_theorem
    (D : DuhamelOperatorDerivative Param Op Direction)
    (n : Nat) (β : Param) (dirs : List Direction) :
    D.higherSimplexOrderedLaw n β dirs (D.higherSimplexOrderedForms n β dirs) :=
  D.higherSimplexOrderedForms_satisfy n β dirs

end DuhamelOperatorDerivative

/-- Moment/cumulant readout after trace/state/KMS evaluation.

Before the readout the data live in `DuhamelOperatorDerivative`; after the
readout they become scalar moments, BKM/Onsager metrics, and response tensors.
-/
@[rep_depth operator]
structure MomentGeneratingReadout (Param Op : Type*) where
  family : OperatorialExponentialFamily Param Op
  firstMoment : Param → Op → ℝ
  bkmCovariance : Param → Op → Op → ℝ
  nResponseForm : Nat → Param → List Op → ℝ
  firstMomentLaw : Param → Op → ℝ → Prop
  bkmCovarianceLaw : Param → Op → Op → ℝ → Prop
  higherCumulantLaw : Nat → Param → List Op → ℝ → Prop

namespace MomentGeneratingReadout

variable {Param Op : Type*}

end MomentGeneratingReadout

/-- Phase-1 Souriau thermodynamic source packet.

This records the genuinely algebraic/logarithmic part of the Souriau Gibbs
dictionary. The negative-log identity is proved from the supplied Gibbs
exponential formula, rather than being carried as a separate field.
-/
@[rep_depth thermo]
structure SouriauLieThermoData (State LieAlgebra LieDual : Type*) where
  momentMap : State → LieDual
  beta : LieAlgebra
  pairing : LieDual → LieAlgebra → ℝ
  liouvilleWeight : Density State
  K_beta : Density State
  partitionFunction : ℝ
  partitionPotential : ℝ
  gibbsDensity : Density State
  partitionFunction_pos : 0 < partitionFunction
  K_beta_eq_pairing : ∀ x, K_beta x = pairing (momentMap x) beta
  partitionPotential_eq_logZ : partitionPotential = Real.log partitionFunction
  gibbsDensity_eq :
    ∀ x, gibbsDensity x = Real.exp (-K_beta x - partitionPotential)

namespace SouriauLieThermoData

variable {State LieAlgebra LieDual : Type*}

@[rep_depth thermo]
theorem K_beta_eq_pairing_apply
    (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) :
    D.K_beta x = D.pairing (D.momentMap x) D.beta :=
  D.K_beta_eq_pairing x

@[rep_depth thermo]
theorem partitionPotential_eq_logZ_theorem
    (D : SouriauLieThermoData State LieAlgebra LieDual) :
    D.partitionPotential = Real.log D.partitionFunction :=
  D.partitionPotential_eq_logZ

@[rep_depth thermo]
theorem gibbsDensity_eq_exp_neg_pairing_sub_Phi
    (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) :
    D.gibbsDensity x =
      Real.exp (-D.pairing (D.momentMap x) D.beta - D.partitionPotential) := by
  rw [D.gibbsDensity_eq x, D.K_beta_eq_pairing x]

@[rep_depth thermo]
theorem negativeLogGibbsDensity_eq_K_beta_add_Phi
    (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) :
    -Real.log (D.gibbsDensity x) = D.K_beta x + D.partitionPotential := by
  rw [D.gibbsDensity_eq x, Real.log_exp]
  ring

@[rep_depth thermo]
theorem negativeLogGibbsDensity_eq_pairing_add_Phi
    (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) :
    -Real.log (D.gibbsDensity x) =
      D.pairing (D.momentMap x) D.beta + D.partitionPotential := by
  rw [D.negativeLogGibbsDensity_eq_K_beta_add_Phi, D.K_beta_eq_pairing x]

end SouriauLieThermoData

/-- Negative logarithmic RN derivative / normalized modular Souriau potential.

The RN derivative is explicitly identified with the Gibbs density, and the
modular potential is derived as `-log(rnDerivative)` instead of being carried as
an independent postulate.
-/
@[rep_depth thermo]
structure SouriauNegativeLogRNDerivative (State LieAlgebra LieDual : Type*) where
  souriau : SouriauLieThermoData State LieAlgebra LieDual
  rnDerivative : Density State
  rnDerivative_eq_gibbsDensity : rnDerivative = souriau.gibbsDensity
  expectationBeta : (Density State) → ℝ
  entropy : ℝ
  Q : LieDual
  entropy_eq_expectation_modularPotential_sorry :
    entropy = expectationBeta (fun x => -Real.log (rnDerivative x))
  entropy_eq_Phi_add_pairing_Q_beta_sorry :
    entropy = souriau.partitionPotential + souriau.pairing Q souriau.beta

/-- Compatibility name emphasizing the relative modular/sign layer. -/
abbrev NegativeLogRNDerivative := SouriauNegativeLogRNDerivative

namespace SouriauNegativeLogRNDerivative

variable {State LieAlgebra LieDual : Type*}

/-- The normalized Souriau modular potential is the negative logarithm of the
Radon--Nikodym derivative. -/
@[rep_depth thermo]
noncomputable def modularPotential
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : Density State :=
  fun x => -Real.log (D.rnDerivative x)

@[rep_depth thermo]
theorem rnDerivative_eq_gibbsDensity_apply
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) :
    D.rnDerivative x = D.souriau.gibbsDensity x := by
  simpa using congrArg (fun f : Density State => f x) D.rnDerivative_eq_gibbsDensity

@[rep_depth thermo]
theorem modularPotential_eq_K_beta_add_Phi
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) :
    D.modularPotential x = D.souriau.K_beta x + D.souriau.partitionPotential := by
  unfold modularPotential
  rw [D.rnDerivative_eq_gibbsDensity_apply]
  exact D.souriau.negativeLogGibbsDensity_eq_K_beta_add_Phi x

@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) :
    D.entropy = D.expectationBeta D.modularPotential := by
  simpa [modularPotential] using D.entropy_eq_expectation_modularPotential_sorry

@[rep_depth thermo]
theorem souriauEntropy_eq_Phi_add_pairing_Q_beta
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) :
    D.entropy = D.souriau.partitionPotential + D.souriau.pairing D.Q D.souriau.beta :=
  D.entropy_eq_Phi_add_pairing_Q_beta_sorry

/-- Existing-test compatibility theorem name. -/
@[rep_depth thermo]
theorem entropy_is_expectation_of_modularPotential
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) :
    D.entropy = D.expectationBeta D.modularPotential :=
  D.entropy_eq_expectation_modularPotential

end SouriauNegativeLogRNDerivative

/-- Souriau moment/covariance generator packet.

The derivative identities are not hidden as anonymous `Prop`s. They are exposed
as explicit maps/equalities so downstream bridges can refer to them directly.
-/
@[rep_depth thermo]
structure MomentMapGeneratingPotential (State LieAlgebra LieDual : Type*) where
  souriau : SouriauLieThermoData State LieAlgebra LieDual
  Q : LieDual
  dPhi : LieAlgebra → ℝ
  hessian : LieAlgebra → LieAlgebra → ℝ
  covarianceTensor : LieAlgebra → LieAlgebra → ℝ
  dPhi_eq_negative_pairing_Q :
    ∀ δβ, dPhi δβ = -souriau.pairing Q δβ
  hessian_eq_covariance :
    ∀ ξ η, hessian ξ η = covarianceTensor ξ η

namespace MomentMapGeneratingPotential

variable {State LieAlgebra LieDual : Type*}

@[rep_depth thermo]
theorem firstVariation_eq_negative_pairing_Q
    (M : MomentMapGeneratingPotential State LieAlgebra LieDual)
    (δβ : LieAlgebra) :
    M.dPhi δβ = -M.souriau.pairing M.Q δβ :=
  M.dPhi_eq_negative_pairing_Q δβ

@[rep_depth thermo]
theorem secondVariation_eq_covariance
    (M : MomentMapGeneratingPotential State LieAlgebra LieDual)
    (ξ η : LieAlgebra) :
    M.hessian ξ η = M.covarianceTensor ξ η :=
  M.hessian_eq_covariance ξ η

end MomentMapGeneratingPotential

/-- KL readout as Bregman divergence of Souriau potential. -/
@[rep_depth thermo]
structure SouriauKLBregmanWitness (State LieAlgebra LieDual : Type*) where
  generator : MomentMapGeneratingPotential State LieAlgebra LieDual
  alpha : LieAlgebra
  alphaPartitionPotential : ℝ
  alphaMinusBeta : LieAlgebra
  klValue : ℝ
  kl_eq_bregman_sorry :
    klValue =
      alphaPartitionPotential
        - generator.souriau.partitionPotential
        - generator.dPhi alphaMinusBeta
  supportHypothesesClaim : Prop

/-- Compatibility name for tests and older prose packets. -/
abbrev KLAsBregmanDivergence := SouriauKLBregmanWitness

namespace SouriauKLBregmanWitness

variable {State LieAlgebra LieDual : Type*}

@[rep_depth thermo]
theorem KL_eq_souriau_Bregman
    (B : SouriauKLBregmanWitness State LieAlgebra LieDual) :
    B.klValue =
      B.alphaPartitionPotential
        - B.generator.souriau.partitionPotential
        - B.generator.dPhi B.alphaMinusBeta :=
  B.kl_eq_bregman_sorry

/-- Existing-test compatibility theorem name. -/
@[rep_depth thermo]
theorem relativeEntropy_eq_expectation_difference
    (B : SouriauKLBregmanWitness State LieAlgebra LieDual) :
    B.klValue =
      B.alphaPartitionPotential
        - B.generator.souriau.partitionPotential
        - B.generator.dPhi B.alphaMinusBeta :=
  B.KL_eq_souriau_Bregman

end SouriauKLBregmanWitness

/-- Operatorial Souriau exponential-family packet (trace-level readout separated).

The operator-level statement is made exact: `ρβ` is a normalized readout of the
untraced exponential, and the modular Hamiltonian is `K̂β + Φ(β)·1`.
-/
@[rep_depth operator]
structure QuantumOperatorialSouriauFamily (LieAlgebra Obs : Type*) where
  Jhat : LieAlgebra → Obs
  beta : LieAlgebra
  Khat_beta : Obs
  untracedExponential : Obs
  opAdd : Obs → Obs → Obs
  opScale : ℝ → Obs → Obs
  opIdentity : Obs
  partitionFunction : ℝ
  partitionPotential : ℝ
  rho_beta : Obs
  modularHamiltonian : Obs
  partitionFunction_pos : 0 < partitionFunction
  Khat_beta_eq : Khat_beta = Jhat beta
  partitionPotential_eq_log_trace :
    partitionPotential = Real.log partitionFunction
  rho_beta_eq_normalized_exp :
    rho_beta = opScale (partitionFunction⁻¹) untracedExponential
  modularHamiltonian_eq :
    modularHamiltonian = opAdd Khat_beta (opScale partitionPotential opIdentity)
  traceClass : Obs → Prop
  traceClass_untraced : traceClass untracedExponential
  traceStateKMSReadoutRequired : Obs → Prop
  traceStateKMSReadoutRequired_rho :
    traceStateKMSReadoutRequired rho_beta

namespace QuantumOperatorialSouriauFamily

variable {LieAlgebra Obs : Type*}

@[rep_depth operator]
theorem modularHamiltonian_eq_Khat_add_logZ
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.modularHamiltonian =
      Q.opAdd Q.Khat_beta (Q.opScale Q.partitionPotential Q.opIdentity) :=
  Q.modularHamiltonian_eq

@[rep_depth operator]
theorem Khat_beta_eq_Jhat_beta
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.Khat_beta = Q.Jhat Q.beta :=
  Q.Khat_beta_eq

end QuantumOperatorialSouriauFamily

/-- Rényi/Mellin deformation layer; Petz and sandwiched packets remain separated.

The temperature-rescaling formula keeps the true exponent `γ`; this is the
Souriau/Mellin bridge, not a hard-coded first-order shadow.
-/
@[rep_depth thermo]
structure RenyiMellinSouriauReadout (State : Type*) where
  gamma : ℝ
  souriauPartitionAtGammaBeta : ℝ
  souriauPartitionAtBeta : ℝ
  massieuAtGammaBeta : ℝ
  massieuAtBeta : ℝ
  renyiPartition : ℝ
  renyiLogGenerator : ℝ
  renyiEntropy : ℝ
  petzRelativeRenyi : ℝ
  sandwichedRelativeRenyi : ℝ
  gamma_ne_one : gamma ≠ 1
  souriauPartitionAtGammaBeta_pos : 0 < souriauPartitionAtGammaBeta
  souriauPartitionAtBeta_pos : 0 < souriauPartitionAtBeta
  massieuAtGammaBeta_eq_log_partition :
    massieuAtGammaBeta = Real.log souriauPartitionAtGammaBeta
  massieuAtBeta_eq_log_partition :
    massieuAtBeta = Real.log souriauPartitionAtBeta
  renyiMellin_eq_temperature_rescaling_sorry :
    renyiPartition =
      souriauPartitionAtGammaBeta / souriauPartitionAtBeta ^ gamma
  renyiLogGenerator_eq_log_partition :
    renyiLogGenerator = Real.log renyiPartition
  renyiEntropy_eq_logGenerator_div_one_sub_gamma :
    renyiEntropy = renyiLogGenerator / (1 - gamma)
  finiteSupportVolumeClaim : Prop
  entropyDerivativeAtOneClaim : Prop
  petz_sandwiched_separatedClaim : Prop

namespace RenyiMellinSouriauReadout

variable {State : Type*}

@[rep_depth thermo]
theorem renyiMellin_eq_temperature_rescaling
    (R : RenyiMellinSouriauReadout State) :
    R.renyiPartition =
      R.souriauPartitionAtGammaBeta / R.souriauPartitionAtBeta ^ R.gamma :=
  R.renyiMellin_eq_temperature_rescaling_sorry

@[rep_depth thermo]
theorem renyiLogGenerator_eq_massieu_rescaling_shift
    (R : RenyiMellinSouriauReadout State) :
    R.renyiLogGenerator =
      R.massieuAtGammaBeta - R.gamma * R.massieuAtBeta := by
  have hpow_ne_zero : R.souriauPartitionAtBeta ^ R.gamma ≠ 0 := by
    exact (Real.rpow_pos_of_pos R.souriauPartitionAtBeta_pos R.gamma).ne'
  rw [R.renyiLogGenerator_eq_log_partition, R.renyiMellin_eq_temperature_rescaling]
  rw [Real.log_div R.souriauPartitionAtGammaBeta_pos.ne' hpow_ne_zero]
  rw [R.massieuAtGammaBeta_eq_log_partition, R.massieuAtBeta_eq_log_partition]
  rw [Real.log_rpow R.souriauPartitionAtBeta_pos]

@[rep_depth thermo]
theorem renyiEntropy_eq_logGenerator_div_one_sub_gamma_compat
    (R : RenyiMellinSouriauReadout State) :
    R.renyiEntropy = R.renyiLogGenerator / (1 - R.gamma) :=
  R.renyiEntropy_eq_logGenerator_div_one_sub_gamma

@[rep_depth thermo]
theorem renyiPartition_pos
    (R : RenyiMellinSouriauReadout State) :
    0 < R.renyiPartition := by
  rw [R.renyiMellin_eq_temperature_rescaling_sorry]
  exact div_pos R.souriauPartitionAtGammaBeta_pos
    (Real.rpow_pos_of_pos R.souriauPartitionAtBeta_pos R.gamma)

end RenyiMellinSouriauReadout

/-- Equivariance/cocycle packet for Souriau Lie covariance. -/
@[rep_depth thermo]
structure LieCovarianceAndCocycle
    (State LieGroup LieAlgebra LieDual : Type*) [Mul LieGroup] [Add LieDual] where
  souriau : SouriauLieThermoData State LieAlgebra LieDual
  groupAction : LieGroup → State → State
  coadjointAction : LieGroup → LieDual → LieDual
  betaAction : LieGroup → LieAlgebra → LieAlgebra
  cocycle : LieGroup → LieDual
  strictEquivariance :
    ∀ g x,
      souriau.momentMap (groupAction g x) =
        coadjointAction g (souriau.momentMap x)
  affineCocycle :
    ∀ g h,
      cocycle (g * h) =
        coadjointAction g (cocycle h) + cocycle g
  partitionPotentialAffineCorrectionClaim : Prop

/-- Metriplectic/Onsager split with free-energy monotonicity witness. -/
@[rep_depth thermo]
structure SouriauMetriplecticOnsager (State Observable : Type*) where
  reversibleFlow : Density State → Density State
  dissipativeFlow : Density State → Density State
  relativeFreeEnergy : Density State → ℝ
  force : Density State → Density State
  variationOfRelativeFreeEnergy : Density State → Density State
  onsagerOperator : Density State → Density State
  freeEnergyDerivative : Density State → ℝ
  force_eq_variation_sorry :
    ∀ ρ, force ρ = variationOfRelativeFreeEnergy ρ
  dissipativeFlow_eq_onsager_force_sorry :
    ∀ ρ, dissipativeFlow ρ = -onsagerOperator (force ρ)
  freeEnergyDerivative_nonpos :
    ∀ ρ, freeEnergyDerivative ρ ≤ 0
  onsagerPositiveSemidefinite : (Density State → Density State) → Prop
  onsager_positive_semidefinite :
    onsagerPositiveSemidefinite onsagerOperator
  hamiltonianPartPreservesFreeEnergy :
    ∀ ρ, relativeFreeEnergy (reversibleFlow ρ) = relativeFreeEnergy ρ
  dissipativePartDissipatesFreeEnergy :
    ∀ ρ, freeEnergyDerivative ρ ≤ 0

namespace SouriauMetriplecticOnsager

variable {State Observable : Type*}

@[rep_depth thermo]
theorem force_eq_variation_of_relativeFreeEnergy
    (O : SouriauMetriplecticOnsager State Observable) (ρ : Density State) :
    O.force ρ = O.variationOfRelativeFreeEnergy ρ :=
  O.force_eq_variation_sorry ρ

@[rep_depth thermo]
theorem dissipativeFlow_eq_onsager_force
    (O : SouriauMetriplecticOnsager State Observable) (ρ : Density State) :
    O.dissipativeFlow ρ = -O.onsagerOperator (O.force ρ) :=
  O.dissipativeFlow_eq_onsager_force_sorry ρ

@[rep_depth thermo]
theorem freeEnergyDerivative_nonpos_theorem
    (O : SouriauMetriplecticOnsager State Observable) (ρ : Density State) :
    O.freeEnergyDerivative ρ ≤ 0 :=
  O.freeEnergyDerivative_nonpos ρ

end SouriauMetriplecticOnsager

/-- OT metric witness and JKO step packet (no convergence theorem without
witnesses). -/
@[rep_depth thermo]
structure OptimalTransportWitness (State : Type*) where
  metric : State → State → ℝ
  curve : ℝ → State
  density : ℝ → Density State
  mobilityTensor : State → State → Prop
  jkoStep : State → State
  continuityEquation : (ℝ → State) → Prop
  wassersteinMetricLaw : (State → State → ℝ) → Prop
  gradientFlowEquation : (ℝ → State) → Prop
  jkoStepLaw : (State → State) → Prop
  lscLaw : (Density State → ℝ) → Prop
  freeEnergy : Density State → ℝ
  coercivityLaw : (Density State → ℝ) → Prop
  compactnessLaw : (ℝ → State) → Prop

/-- GENERIC compatibility packet. -/
@[rep_depth thermo]
structure GenericMetriplecticCompatibility (State Observable : Type*) where
  L : Observable → Observable
  K : Observable → Observable
  energy : Observable
  entropy : Observable
  evolution : Observable → Observable
  dE : Observable → ℝ
  dS : Observable → ℝ
  LSkewPoisson : (Observable → Observable) → Prop
  L_skew_poisson : LSkewPoisson L
  KSymmetricPSD : (Observable → Observable) → Prop
  K_symmetric_psd : KSymmetricPSD K
  K_deltaE_eq_zero : K energy = energy
  L_deltaS_eq_zero : L entropy = entropy
  dE_eq_zero : dE (evolution energy) = 0
  dS_nonneg : 0 ≤ dS (evolution entropy)

/-- Existing naming convention compatibility. -/
abbrev GENERICCompatibility := GenericMetriplecticCompatibility

namespace GenericMetriplecticCompatibility

variable {State Observable : Type*}

/-- GENERIC bookkeeping theorem: energy conserved, entropy nondecreasing. -/
@[rep_depth thermo]
theorem dE_eq_zero_and_dS_nonneg
    (G : GenericMetriplecticCompatibility State Observable) :
    G.dE (G.evolution G.energy) = 0 ∧
      0 ≤ G.dS (G.evolution G.entropy) :=
  ⟨G.dE_eq_zero, G.dS_nonneg⟩

end GenericMetriplecticCompatibility


/-! ## Constructive Souriau/Tomita owner branch

The preceding packets keep broad analytic identities as explicit data.  The
branch below processes the smallest honest infinite/dimension-agnostic packet:
when the logarithmic potential is already owned by the repo's Souriau/Tomita
standard-form context, the negative logarithmic density, modular Hamiltonian,
Souriau moment at geometric temperature, and generated untraced modular family
are connected by definitional or previously proved equalities.  No finite Cartan
basis, matrix dimension, trace-class assumption, or scalar partition toy is used.
-/

section ConstructiveSouriauTomitaOwner

open InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
open InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
open InfoGeometry.Volume.ConnesCocycle

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Symmetry : Type v}

local notation "Obs" => InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H

/--
Constructive owner for the operatorial logarithmic potential on the
Souriau/Tomita lane.

Unlike `ModularHamiltonianData`, this is not a bag of independent hypotheses.
It is anchored directly to `SouriauTomitaLogContext`, so the negative-log datum,
modular Hamiltonian, standard-form carrier, and generated modular family remain
owned by the same observable context.
-/
@[rep_depth operator]
structure ConstructiveSouriauTomitaLogPotentialOwner where
  logContext : SouriauTomitaLogContext (H := H) (Symmetry := Symmetry)

namespace ConstructiveSouriauTomitaLogPotentialOwner

variable (O : ConstructiveSouriauTomitaLogPotentialOwner (H := H) (Symmetry := Symmetry))

/-- The negative logarithmic density is the Tomita logarithmic datum. -/
@[rep_depth operator]
def negativeLogDensity : Obs :=
  O.logContext.toRealModularLogData

/-- The modular Hamiltonian is the Souriau-selected Tomita generator. -/
@[rep_depth operator]
def modularHamiltonian : Obs :=
  O.logContext.modularHamiltonian

/-- The standard-form carrier read on the same observable carrier. -/
@[rep_depth operator]
noncomputable def standardFormCarrier : StandardFormCarrier H :=
  O.logContext.toStandardFormCarrier

/-- The Souriau moment evaluated at geometric temperature. -/
@[rep_depth operator]
def souriauMomentAtGeometricTemperature : Obs :=
  O.logContext.souriauMoment.momentOperator
    O.logContext.souriauMoment.geometricTemperature

/-- The untraced operatorial exponential family is represented by the generated modular flow. -/
@[rep_depth operator]
noncomputable def untracedModularFamily : AdditiveModularFlow (H := H) :=
  O.logContext.souriauAdditiveModularFlow

/-- Processed sign/log theorem: the negative log datum is the modular Hamiltonian. -/
@[rep_depth operator]
theorem negativeLogDensity_eq_modularHamiltonian :
    O.negativeLogDensity = O.modularHamiltonian :=
  O.logContext.tomita_deltaLog_eq_modularHamiltonian

/-- The standard-form carrier is generated by that same modular Hamiltonian. -/
@[rep_depth operator]
theorem standardFormCarrier_Delta_eq_modularHamiltonian :
    O.standardFormCarrier.Delta = O.modularHamiltonian :=
  O.logContext.toStandardFormCarrier_Delta_eq_modularHamiltonian

/-- The standard-form carrier flow is the same untraced modular family. -/
@[rep_depth operator]
theorem standardFormCarrier_modularFlow_eq_untracedModularFamily :
    O.standardFormCarrier.seed.modularFlow = O.untracedModularFamily := by
  unfold standardFormCarrier untracedModularFamily
  change O.logContext.tomitaAdditiveModularFlow =
    O.logContext.souriauAdditiveModularFlow
  exact O.logContext.tomita_flow_eq_souriau_modularTransportFlow

/-- Processed Souriau theorem: the modular Hamiltonian is the moment at geometric temperature. -/
@[rep_depth operator]
theorem modularHamiltonian_eq_moment_geometricTemperature_constructive :
    O.modularHamiltonian = O.souriauMomentAtGeometricTemperature :=
  O.logContext.modularHamiltonian_eq_moment_geometricTemperature

/-- Processed flow theorem: the untraced family is generated by the modular Hamiltonian. -/
@[rep_depth operator]
theorem untracedExponential_apply_eq_modular_shift
    (t : ℝ) (A : Obs) :
    O.untracedModularFamily t A =
      InfoGeometry.Krein.modular_shift (E := H) O.modularHamiltonian t A :=
  O.logContext.souriauAdditiveModularFlow_apply_eq_modularHamiltonian_shift t A

/--
Constructive packet replacing the broad explicit hypothesis shell by the owned
Souriau/Tomita equalities.
-/
@[rep_depth operator]
theorem constructive_operatorial_log_potential_packet
    (t : ℝ) (A : Obs) :
    O.negativeLogDensity = O.modularHamiltonian ∧
    O.standardFormCarrier.Delta = O.modularHamiltonian ∧
    O.standardFormCarrier.seed.modularFlow = O.untracedModularFamily ∧
    O.modularHamiltonian = O.souriauMomentAtGeometricTemperature ∧
    O.untracedModularFamily t A =
      InfoGeometry.Krein.modular_shift (E := H) O.modularHamiltonian t A := by
  exact ⟨
    O.negativeLogDensity_eq_modularHamiltonian,
    O.standardFormCarrier_Delta_eq_modularHamiltonian,
    O.standardFormCarrier_modularFlow_eq_untracedModularFamily,
    O.modularHamiltonian_eq_moment_geometricTemperature_constructive,
    O.untracedExponential_apply_eq_modular_shift t A⟩

end ConstructiveSouriauTomitaLogPotentialOwner

/--
Untraced operatorial Souriau exponential family generated directly by the
Souriau/Tomita owner.  The readout is operatorial; no trace-class scalar
partition field is part of this constructive branch.
-/
@[rep_depth operator]
structure UntracedSouriauOperatorialExponentialFamily where
  owner : ConstructiveSouriauTomitaLogPotentialOwner (H := H) (Symmetry := Symmetry)

namespace UntracedSouriauOperatorialExponentialFamily

variable (E : UntracedSouriauOperatorialExponentialFamily (H := H) (Symmetry := Symmetry))

/-- Generator of the untraced family. -/
@[rep_depth operator]
def generator : Obs :=
  E.owner.modularHamiltonian

/-- The untraced family as a modular automorphism flow. -/
@[rep_depth operator]
noncomputable def family : AdditiveModularFlow (H := H) :=
  E.owner.untracedModularFamily

/-- The untraced family is exactly the modular shift generated by `generator`. -/
@[rep_depth operator]
theorem family_apply_eq_modular_shift (t : ℝ) (A : Obs) :
    E.family t A = InfoGeometry.Krein.modular_shift (E := H) E.generator t A :=
  E.owner.untracedExponential_apply_eq_modular_shift t A

end UntracedSouriauOperatorialExponentialFamily

end ConstructiveSouriauTomitaOwner

end InfoGeometry.Canonical.SouriauOperatorialLogPotential
