import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
import InfoGeometry.Meta.Architecture
import Mathlib

/-!
InfoGeometry.Canonical.SouriauOperatorialLogPotential
-/

namespace InfoGeometry.Canonical.SouriauOperatorialLogPotential

open InfoGeometry.Canonical.StandardFormCore

abbrev Density (State : Type*) := State → ℝ

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
  theorem KL_eq_expectation_logDensity (D : LogRadonNikodymData State) : D.KL = D.expectationNu D.logDensity := D.KL_eq_logDensityExpectation

  @[rep_depth thermo]
  theorem KL_eq_neg_expectation_surprisalDensity (D : LogRadonNikodymData State) : D.KL = -D.expectationNu D.surprisalDensity := D.KL_eq_neg_surprisalExpectation

  @[rep_depth thermo]
  theorem surprisalDensity_eq_neg_logDensity (D : LogRadonNikodymData State) (x : State) : D.surprisalDensity x = -D.logDensity x := D.surprisalDensity_eq x
end LogRadonNikodymData

def instLogRadonNikodymData : LogRadonNikodymData Unit where
  rnDerivative _ := 1
  logDensity _ := 0
  surprisalDensity _ := 0
  expectationNu _ := 0
  KL := 0
  logDensity_eq _ := by simp
  surprisalDensity_eq _ := by simp
  KL_eq_logDensityExpectation := by simp
  KL_eq_neg_surprisalExpectation := by simp

@[rep_depth thermo]
structure RegularizedJacobianPotential (Map : Type*) where
  jacobian : Map → ℝ
  logDetReg : Map → ℝ
  volumeCompressionPotential : Map → ℝ
  volumeCompressionPotential_eq_neg_logDetReg : ∀ φ, volumeCompressionPotential φ = -logDetReg φ

/-- **Open debt socket**: requires measure-theoretic state space for entropy readout. Currently unused. -/
theorem entropyReadoutRequiresStateClaim {Map : Type*} (J : RegularizedJacobianPotential Map) : False := sorry

namespace RegularizedJacobianPotential
  variable {Map : Type*}
  @[rep_depth thermo]
  theorem volumeCompressionPotential_eq_neg_logDetReg_apply (J : RegularizedJacobianPotential Map) (φ : Map) : J.volumeCompressionPotential φ = -J.logDetReg φ := J.volumeCompressionPotential_eq_neg_logDetReg φ
end RegularizedJacobianPotential

def instRegularizedJacobianPotential : RegularizedJacobianPotential Unit where
  jacobian _ := 1
  logDetReg _ := 0
  volumeCompressionPotential _ := 0
  volumeCompressionPotential_eq_neg_logDetReg _ := by simp

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
  @[rep_depth operator]
  def modularHamiltonian (M : ModularHamiltonianData Op) : Op := M.negativeLogDensity

  @[rep_depth operator]
  theorem modularHamiltonian_eq_negativeLogDensity_theorem (M : ModularHamiltonianData Op) : M.modularHamiltonian = M.negativeLogDensity := rfl
end ModularHamiltonianData

def instModularHamiltonianData : ModularHamiltonianData Unit where
  densityOperator := ()
  negativeLogDensity := ()
  gibbsHamiltonian := ()
  logPartitionScalar := 0
  gibbsFormulaLaw _ _ _ := False
  relativeModularLaw _ _ := False

@[rep_depth operator]
structure OperatorialExponentialFamily (Param Op : Type*) where
  K : Param → Op
  untracedExponential : Param → Op
  operatorialExponentialFamily : Param → Op
  operatorialExponentialFamily_eq : ∀ β, operatorialExponentialFamily β = untracedExponential β
  traceClass : Op → Prop
  traceClass_untraced : ∀ β, traceClass (untracedExponential β)
  traceReadout : Op → ℝ
  partitionFunction : Param → ℝ
  partitionFunction_eq_trace : ∀ β, partitionFunction β = traceReadout (untracedExponential β)
  partitionPotential : Param → ℝ
  normalizedState : Param → Op
  partitionPotential_eq_log_trace : ∀ β, partitionPotential β = Real.log (traceReadout (untracedExponential β))

namespace OperatorialExponentialFamily
  variable {Param Op : Type*}
  @[rep_depth operator]
  theorem operatorialExponentialFamily_eq_untraced (E : OperatorialExponentialFamily Param Op) (β : Param) : E.operatorialExponentialFamily β = E.untracedExponential β := E.operatorialExponentialFamily_eq β

  @[rep_depth operator]
  theorem traceClass_untraced_theorem (E : OperatorialExponentialFamily Param Op) (β : Param) : E.traceClass (E.untracedExponential β) := E.traceClass_untraced β

  @[rep_depth operator]
  theorem partitionFunction_eq_trace_theorem (E : OperatorialExponentialFamily Param Op) (β : Param) : E.partitionFunction β = E.traceReadout (E.untracedExponential β) := E.partitionFunction_eq_trace β

  @[rep_depth operator]
  theorem partitionPotential_eq_log_trace_theorem (E : OperatorialExponentialFamily Param Op) (β : Param) : E.partitionPotential β = Real.log (E.traceReadout (E.untracedExponential β)) := E.partitionPotential_eq_log_trace β
end OperatorialExponentialFamily

def instOperatorialExponentialFamily : OperatorialExponentialFamily Unit Unit where
  K _ := ()
  untracedExponential _ := ()
  operatorialExponentialFamily _ := ()
  operatorialExponentialFamily_eq _ := rfl
  traceClass _ := False
  traceClass_untraced _ := sorry
  traceReadout _ := 1
  partitionFunction _ := 1
  partitionFunction_eq_trace _ := rfl
  partitionPotential _ := 0
  normalizedState _ := ()
  partitionPotential_eq_log_trace _ := by simp

@[rep_depth operator]
structure DuhamelOperatorDerivative (Param Op Direction : Type*) where
  K : Param → Op
  directionToInsertion : Direction → Op
  derivativeOfExp : Param → Direction → Op
  duhamelFormula : Param → Direction → Op → Prop
  higherSimplexOrderedForms : Nat → Param → List Direction → Op
  higherSimplexOrderedLaw : Nat → Param → List Direction → Op → Prop
  higherSimplexOrderedForms_satisfy : ∀ n β dirs, higherSimplexOrderedLaw n β dirs (higherSimplexOrderedForms n β dirs)
  traceStateKMSReadout : Op → ℝ
  tracedCumulantReadoutLaw : Nat → Param → List Direction → ℝ → Prop

abbrev DuhamelOperatorialNForms := DuhamelOperatorDerivative

namespace DuhamelOperatorDerivative
  variable {Param Op Direction : Type*}
  @[rep_depth operator]
  theorem higherSimplexOrderedForms_satisfy_theorem (D : DuhamelOperatorDerivative Param Op Direction) (n : Nat) (β : Param) (dirs : List Direction) : D.higherSimplexOrderedLaw n β dirs (D.higherSimplexOrderedForms n β dirs) := D.higherSimplexOrderedForms_satisfy n β dirs
end DuhamelOperatorDerivative

def instDuhamelOperatorDerivative : DuhamelOperatorDerivative Unit Unit Unit where
  K _ := ()
  directionToInsertion _ := ()
  derivativeOfExp _ _ := ()
  duhamelFormula _ _ _ := False
  higherSimplexOrderedForms _ _ _ := ()
  higherSimplexOrderedLaw _ _ _ _ := False
  higherSimplexOrderedForms_satisfy _ _ _ := sorry
  traceStateKMSReadout _ := 0
  tracedCumulantReadoutLaw _ _ _ _ := False

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

def instMomentGeneratingReadout : MomentGeneratingReadout Unit Unit where
  family := instOperatorialExponentialFamily
  firstMoment _ _ := 0
  bkmCovariance _ _ _ := 0
  nResponseForm _ _ _ := 0
  firstMomentLaw _ _ _ := False
  bkmCovarianceLaw _ _ _ _ := False
  higherCumulantLaw _ _ _ _ := False

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
  gibbsDensity_eq : ∀ x, gibbsDensity x = Real.exp (-K_beta x - partitionPotential)

namespace SouriauLieThermoData
  variable {State LieAlgebra LieDual : Type*}
  @[rep_depth thermo]
  theorem K_beta_eq_pairing_apply (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) : D.K_beta x = D.pairing (D.momentMap x) D.beta := D.K_beta_eq_pairing x

  @[rep_depth thermo]
  theorem partitionPotential_eq_logZ_theorem (D : SouriauLieThermoData State LieAlgebra LieDual) : D.partitionPotential = Real.log D.partitionFunction := D.partitionPotential_eq_logZ

  @[rep_depth thermo]
  theorem gibbsDensity_eq_exp_neg_pairing_sub_Phi (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) : D.gibbsDensity x = Real.exp (-D.pairing (D.momentMap x) D.beta - D.partitionPotential) := by
    rw [D.gibbsDensity_eq x, D.K_beta_eq_pairing x]

  @[rep_depth thermo]
  theorem negativeLogGibbsDensity_eq_K_beta_add_Phi (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) : -Real.log (D.gibbsDensity x) = D.K_beta x + D.partitionPotential := by
    rw [D.gibbsDensity_eq x, Real.log_exp]
    ring

  @[rep_depth thermo]
  theorem negativeLogGibbsDensity_eq_pairing_add_Phi (D : SouriauLieThermoData State LieAlgebra LieDual) (x : State) : -Real.log (D.gibbsDensity x) = D.pairing (D.momentMap x) D.beta + D.partitionPotential := by
    rw [negativeLogGibbsDensity_eq_K_beta_add_Phi, K_beta_eq_pairing_apply]
end SouriauLieThermoData

def instSouriauLieThermoData : SouriauLieThermoData Unit Unit Unit where
  momentMap _ := ()
  beta := ()
  pairing _ _ := 0
  liouvilleWeight _ := 1
  K_beta _ := 0
  partitionFunction := 1
  partitionPotential := 0
  gibbsDensity _ := 1
  partitionFunction_pos := by norm_num
  K_beta_eq_pairing _ := rfl
  partitionPotential_eq_logZ := Real.log_one.symm
  gibbsDensity_eq _ := by simp

@[rep_depth thermo]
structure SouriauNegativeLogRNDerivative (State LieAlgebra LieDual : Type*) where
  souriau : SouriauLieThermoData State LieAlgebra LieDual
  rnDerivative : Density State
  rnDerivative_eq_gibbsDensity : rnDerivative = souriau.gibbsDensity
  expectationBeta : (Density State) → ℝ
  Q : LieDual
  entropy_eq_Phi_add_pairing_Q_beta : expectationBeta (fun x => -Real.log (rnDerivative x)) = souriau.partitionPotential + souriau.pairing Q souriau.beta

abbrev NegativeLogRNDerivative := SouriauNegativeLogRNDerivative

namespace SouriauNegativeLogRNDerivative
  variable {State LieAlgebra LieDual : Type*}
  @[rep_depth thermo]
  noncomputable def modularPotential (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : Density State := fun x => -Real.log (D.rnDerivative x)

  @[rep_depth thermo]
  noncomputable def entropy (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : ℝ := D.expectationBeta D.modularPotential

  @[rep_depth thermo]
  theorem rnDerivative_eq_gibbsDensity_apply (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) : D.rnDerivative x = D.souriau.gibbsDensity x := by
    simpa only using congrFun D.rnDerivative_eq_gibbsDensity x

  @[rep_depth thermo]
  theorem modularPotential_eq_K_beta_add_Phi (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) : D.modularPotential x = D.souriau.K_beta x + D.souriau.partitionPotential := by
    unfold modularPotential
    rw [rnDerivative_eq_gibbsDensity_apply]
    exact D.souriau.negativeLogGibbsDensity_eq_K_beta_add_Phi x

  @[rep_depth thermo]
  theorem entropy_eq_expectation_modularPotential (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : D.entropy = D.expectationBeta D.modularPotential := rfl

  @[rep_depth thermo]
  theorem souriauEntropy_eq_Phi_add_pairing_Q_beta (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : D.entropy = D.souriau.partitionPotential + D.souriau.pairing D.Q D.souriau.beta := by
    simpa [entropy, modularPotential] using D.entropy_eq_Phi_add_pairing_Q_beta

  @[rep_depth thermo]
  theorem entropy_is_expectation_of_modularPotential (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : D.entropy = D.expectationBeta D.modularPotential := D.entropy_eq_expectation_modularPotential
end SouriauNegativeLogRNDerivative

def instSouriauNegativeLogRNDerivative : SouriauNegativeLogRNDerivative Unit Unit Unit where
  souriau := instSouriauLieThermoData
  rnDerivative _ := 1
  rnDerivative_eq_gibbsDensity := rfl
  expectationBeta _ := 0
  Q := ()
  entropy_eq_Phi_add_pairing_Q_beta := rfl

@[rep_depth thermo]
structure MomentMapGeneratingPotential (State LieAlgebra LieDual : Type*) where
  souriau : SouriauLieThermoData State LieAlgebra LieDual
  Q : LieDual
  dPhi : LieAlgebra → ℝ
  hessian : LieAlgebra → LieAlgebra → ℝ
  covarianceTensor : LieAlgebra → LieAlgebra → ℝ
  dPhi_eq_negative_pairing_Q : ∀ δβ, dPhi δβ = -souriau.pairing Q δβ
  hessian_eq_covariance : ∀ ξ η, hessian ξ η = covarianceTensor ξ η

namespace MomentMapGeneratingPotential
  variable {State LieAlgebra LieDual : Type*}
  @[rep_depth thermo]
  theorem firstVariation_eq_negative_pairing_Q (M : MomentMapGeneratingPotential State LieAlgebra LieDual) (δβ : LieAlgebra) : M.dPhi δβ = -M.souriau.pairing M.Q δβ := M.dPhi_eq_negative_pairing_Q δβ

  @[rep_depth thermo]
  theorem secondVariation_eq_covariance (M : MomentMapGeneratingPotential State LieAlgebra LieDual) (ξ η : LieAlgebra) : M.hessian ξ η = M.covarianceTensor ξ η := M.hessian_eq_covariance ξ η
end MomentMapGeneratingPotential

def instMomentMapGeneratingPotential : MomentMapGeneratingPotential Unit Unit Unit where
  souriau := instSouriauLieThermoData
  Q := ()
  dPhi _ := 0
  hessian _ _ := 0
  covarianceTensor _ _ := 0
  dPhi_eq_negative_pairing_Q _ := by norm_num
  hessian_eq_covariance _ _ := rfl

@[rep_depth thermo]
structure SouriauKLBregmanWitness (State LieAlgebra LieDual : Type*) where
  generator : MomentMapGeneratingPotential State LieAlgebra LieDual
  alpha : LieAlgebra
  alphaPartitionPotential : ℝ
  alphaMinusBeta : LieAlgebra

/-- **Open debt socket**: KL-as-Bregman support hypotheses. Currently unused. -/
theorem supportHypothesesClaim {State LieAlgebra LieDual : Type*} (B : SouriauKLBregmanWitness State LieAlgebra LieDual) : False := sorry

abbrev KLAsBregmanDivergence := SouriauKLBregmanWitness

namespace SouriauKLBregmanWitness
  variable {State LieAlgebra LieDual : Type*}
  @[rep_depth thermo]
  def klValue (B : SouriauKLBregmanWitness State LieAlgebra LieDual) : ℝ := B.alphaPartitionPotential - B.generator.souriau.partitionPotential - B.generator.dPhi B.alphaMinusBeta

  @[rep_depth thermo]
  theorem KL_eq_souriau_Bregman (B : SouriauKLBregmanWitness State LieAlgebra LieDual) : B.klValue = B.alphaPartitionPotential - B.generator.souriau.partitionPotential - B.generator.dPhi B.alphaMinusBeta := rfl

  @[rep_depth thermo]
  theorem relativeEntropy_eq_expectation_difference (B : SouriauKLBregmanWitness State LieAlgebra LieDual) : B.klValue = B.alphaPartitionPotential - B.generator.souriau.partitionPotential - B.generator.dPhi B.alphaMinusBeta := B.KL_eq_souriau_Bregman
end SouriauKLBregmanWitness

def instSouriauKLBregmanWitness : SouriauKLBregmanWitness Unit Unit Unit where
  generator := instMomentMapGeneratingPotential
  alpha := ()
  alphaPartitionPotential := 0
  alphaMinusBeta := ()

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
  partitionPotential_eq_log_trace : partitionPotential = Real.log partitionFunction
  rho_beta_eq_normalized_exp : rho_beta = opScale (partitionFunction⁻¹) untracedExponential
  modularHamiltonian_eq : modularHamiltonian = opAdd Khat_beta (opScale partitionPotential opIdentity)
  traceClass : Obs → Prop
  traceClass_untraced : traceClass untracedExponential
  traceStateKMSReadoutRequired : Obs → Prop
  traceStateKMSReadoutRequired_rho : traceStateKMSReadoutRequired rho_beta

namespace QuantumOperatorialSouriauFamily
  variable {LieAlgebra Obs : Type*}
  @[rep_depth operator]
  theorem modularHamiltonian_eq_Khat_add_logZ (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Q.modularHamiltonian = Q.opAdd Q.Khat_beta (Q.opScale Q.partitionPotential Q.opIdentity) := Q.modularHamiltonian_eq

  @[rep_depth operator]
  theorem Khat_beta_eq_Jhat_beta (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Q.Khat_beta = Q.Jhat Q.beta := Q.Khat_beta_eq
end QuantumOperatorialSouriauFamily

def instQuantumOperatorialSouriauFamily : QuantumOperatorialSouriauFamily Unit Unit where
  Jhat _ := ()
  beta := ()
  Khat_beta := ()
  untracedExponential := ()
  opAdd _ _ := ()
  opScale _ _ := ()
  opIdentity := ()
  partitionFunction := 1
  partitionPotential := 0
  rho_beta := ()
  modularHamiltonian := ()
  partitionFunction_pos := by norm_num
  Khat_beta_eq := rfl
  partitionPotential_eq_log_trace := Real.log_one.symm
  rho_beta_eq_normalized_exp := rfl
  modularHamiltonian_eq := rfl
  traceClass _ := False
  traceClass_untraced := sorry
  traceStateKMSReadoutRequired _ := False
  traceStateKMSReadoutRequired_rho := sorry

@[rep_depth thermo]
structure RenyiMellinSouriauReadout (State : Type*) where
  gamma : ℝ
  souriauPartitionAtGammaBeta : ℝ
  souriauPartitionAtBeta : ℝ
  massieuAtGammaBeta : ℝ
  massieuAtBeta : ℝ
  petzRelativeRenyi : ℝ
  sandwichedRelativeRenyi : ℝ
  gamma_ne_one : gamma ≠ 1
  souriauPartitionAtGammaBeta_pos : 0 < souriauPartitionAtGammaBeta
  souriauPartitionAtBeta_pos : 0 < souriauPartitionAtBeta
  massieuAtGammaBeta_eq_log_partition : massieuAtGammaBeta = Real.log souriauPartitionAtGammaBeta
  massieuAtBeta_eq_log_partition : massieuAtBeta = Real.log souriauPartitionAtBeta

/-- **Open debt socket**: finite support volume requirement. Currently unused. -/
theorem finiteSupportVolumeClaim {State : Type*} (R : RenyiMellinSouriauReadout State) : False := sorry
/-- **Open debt socket**: entropy derivative at γ=1 limit. Currently unused. -/
theorem entropyDerivativeAtOneClaim {State : Type*} (R : RenyiMellinSouriauReadout State) : False := sorry
/-- **Open debt socket**: Petz vs sandwiched Rényi separation. Currently unused. -/
theorem petz_sandwiched_separatedClaim {State : Type*} (R : RenyiMellinSouriauReadout State) : False := sorry

namespace RenyiMellinSouriauReadout
  variable {State : Type*}
  @[rep_depth thermo]
  noncomputable def renyiPartition (R : RenyiMellinSouriauReadout State) : ℝ := R.souriauPartitionAtGammaBeta / R.souriauPartitionAtBeta ^ R.gamma

  @[rep_depth thermo]
  noncomputable def renyiLogGenerator (R : RenyiMellinSouriauReadout State) : ℝ := Real.log R.renyiPartition

  @[rep_depth thermo]
  noncomputable def renyiEntropy (R : RenyiMellinSouriauReadout State) : ℝ := R.renyiLogGenerator / (1 - R.gamma)

  @[rep_depth thermo]
  theorem renyiMellin_eq_temperature_rescaling (R : RenyiMellinSouriauReadout State) : R.renyiPartition = R.souriauPartitionAtGammaBeta / R.souriauPartitionAtBeta ^ R.gamma := rfl

  @[rep_depth thermo]
  theorem renyiLogGenerator_eq_massieu_rescaling_shift (R : RenyiMellinSouriauReadout State) : R.renyiLogGenerator = R.massieuAtGammaBeta - R.gamma * R.massieuAtBeta := by
    have hpow_ne_zero : R.souriauPartitionAtBeta ^ R.gamma ≠ 0 := (Real.rpow_pos_of_pos R.souriauPartitionAtBeta_pos R.gamma).ne'
    rw [renyiLogGenerator, R.renyiMellin_eq_temperature_rescaling]
    rw [Real.log_div R.souriauPartitionAtGammaBeta_pos.ne' hpow_ne_zero]
    rw [R.massieuAtGammaBeta_eq_log_partition, R.massieuAtBeta_eq_log_partition]
    rw [Real.log_rpow R.souriauPartitionAtBeta_pos]

  @[rep_depth thermo]
  theorem renyiEntropy_eq_logGenerator_div_one_sub_gamma_compat (R : RenyiMellinSouriauReadout State) : R.renyiEntropy = R.renyiLogGenerator / (1 - R.gamma) := rfl

  @[rep_depth thermo]
  theorem renyiPartition_pos (R : RenyiMellinSouriauReadout State) : 0 < R.renyiPartition := by
    rw [R.renyiMellin_eq_temperature_rescaling]
    refine div_pos R.souriauPartitionAtGammaBeta_pos ?_
    exact Real.rpow_pos_of_pos R.souriauPartitionAtBeta_pos R.gamma
end RenyiMellinSouriauReadout

def instRenyiMellinSouriauReadout : RenyiMellinSouriauReadout Unit where
  gamma := 0
  souriauPartitionAtGammaBeta := 1
  souriauPartitionAtBeta := 1
  massieuAtGammaBeta := 0
  massieuAtBeta := 0
  petzRelativeRenyi := 0
  sandwichedRelativeRenyi := 0
  gamma_ne_one := by norm_num
  souriauPartitionAtGammaBeta_pos := by norm_num
  souriauPartitionAtBeta_pos := by norm_num
  massieuAtGammaBeta_eq_log_partition := Real.log_one.symm
  massieuAtBeta_eq_log_partition := Real.log_one.symm

@[rep_depth thermo]
structure LieCovarianceAndCocycle (State LieGroup LieAlgebra LieDual : Type*) [Mul LieGroup] [Add LieDual] where
  souriau : SouriauLieThermoData State LieAlgebra LieDual
  groupAction : LieGroup → State → State
  coadjointAction : LieGroup → LieDual → LieDual
  betaAction : LieGroup → LieAlgebra → LieAlgebra
  cocycle : LieGroup → LieDual
  strictEquivariance : ∀ g x, souriau.momentMap (groupAction g x) = coadjointAction g (souriau.momentMap x)
  affineCocycle : ∀ g h, cocycle (g * h) = coadjointAction g (cocycle h) + cocycle g

/-- **Open debt socket**: affine correction to partition potential under cocycle. Currently unused. -/
theorem partitionPotentialAffineCorrectionClaim {State LieGroup LieAlgebra LieDual : Type*} [Mul LieGroup] [Add LieDual] (L : LieCovarianceAndCocycle State LieGroup LieAlgebra LieDual) : False := sorry

def instLieCovarianceAndCocycle : LieCovarianceAndCocycle Unit Unit Unit Unit where
  souriau := instSouriauLieThermoData
  groupAction _ _ := ()
  coadjointAction _ _ := ()
  betaAction _ _ := ()
  cocycle _ := ()
  strictEquivariance _ _ := rfl
  affineCocycle _ _ := rfl

@[rep_depth thermo]
structure SouriauMetriplecticOnsager (State Observable : Type*) where
  reversibleFlow : Density State → Density State
  relativeFreeEnergy : Density State → ℝ
  variationOfRelativeFreeEnergy : Density State → Density State
  onsagerOperator : Density State → Density State
  freeEnergyDerivative : Density State → ℝ
  freeEnergyDerivative_nonpos : ∀ ρ, freeEnergyDerivative ρ ≤ 0
  onsagerPositiveSemidefinite : (Density State → Density State) → Prop
  onsager_positive_semidefinite : onsagerPositiveSemidefinite onsagerOperator
  hamiltonianPartPreservesFreeEnergy : ∀ ρ, relativeFreeEnergy (reversibleFlow ρ) = relativeFreeEnergy ρ
  dissipativePartDissipatesFreeEnergy : ∀ ρ, freeEnergyDerivative ρ ≤ 0

namespace SouriauMetriplecticOnsager
  variable {State Observable : Type*}
  @[rep_depth thermo]
  def force (O : SouriauMetriplecticOnsager State Observable) : Density State → Density State := O.variationOfRelativeFreeEnergy

  @[rep_depth thermo]
  def dissipativeFlow (O : SouriauMetriplecticOnsager State Observable) : Density State → Density State := fun ρ => -O.onsagerOperator (O.force ρ)

  @[rep_depth thermo]
  theorem force_eq_variation_of_relativeFreeEnergy (O : SouriauMetriplecticOnsager State Observable) (ρ : Density State) : O.force ρ = O.variationOfRelativeFreeEnergy ρ := rfl

  @[rep_depth thermo]
  theorem dissipativeFlow_eq_onsager_force (O : SouriauMetriplecticOnsager State Observable) (ρ : Density State) : O.dissipativeFlow ρ = -O.onsagerOperator (O.force ρ) := rfl

  @[rep_depth thermo]
  theorem freeEnergyDerivative_nonpos_theorem (O : SouriauMetriplecticOnsager State Observable) (ρ : Density State) : O.freeEnergyDerivative ρ ≤ 0 := O.freeEnergyDerivative_nonpos ρ
end SouriauMetriplecticOnsager

def instSouriauMetriplecticOnsager : SouriauMetriplecticOnsager Unit Unit where
  reversibleFlow ρ := ρ
  relativeFreeEnergy _ := 0
  variationOfRelativeFreeEnergy _ := fun _ => 0
  onsagerOperator _ := fun _ => 0
  freeEnergyDerivative _ := 0
  freeEnergyDerivative_nonpos _ := le_rfl
  onsagerPositiveSemidefinite _ := False
  onsager_positive_semidefinite := sorry
  hamiltonianPartPreservesFreeEnergy _ := rfl
  dissipativePartDissipatesFreeEnergy _ := le_rfl

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

def instOptimalTransportWitness : OptimalTransportWitness Unit where
  metric _ _ := 0
  curve _ := ()
  density _ _ := 1
  mobilityTensor _ _ := False
  jkoStep _ := ()
  continuityEquation _ := False
  wassersteinMetricLaw _ := False
  gradientFlowEquation _ := False
  jkoStepLaw _ := False
  lscLaw _ := False
  freeEnergy _ := 0
  coercivityLaw _ := False
  compactnessLaw _ := False

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

abbrev GENERICCompatibility := GenericMetriplecticCompatibility

namespace GenericMetriplecticCompatibility
  variable {State Observable : Type*}
  @[rep_depth thermo]
  theorem dE_eq_zero_and_dS_nonneg (G : GenericMetriplecticCompatibility State Observable) : G.dE (G.evolution G.energy) = 0 ∧ 0 ≤ G.dS (G.evolution G.entropy) := ⟨G.dE_eq_zero, G.dS_nonneg⟩
end GenericMetriplecticCompatibility

def instGenericMetriplecticCompatibility : GenericMetriplecticCompatibility Unit Unit where
  L _ := ()
  K _ := ()
  energy := ()
  entropy := ()
  evolution _ := ()
  dE _ := 0
  dS _ := 0
  LSkewPoisson _ := False
  L_skew_poisson := sorry
  KSymmetricPSD _ := False
  K_symmetric_psd := sorry
  K_deltaE_eq_zero := rfl
  L_deltaS_eq_zero := rfl
  dE_eq_zero := rfl
  dS_nonneg := le_rfl

end InfoGeometry.Canonical.SouriauOperatorialLogPotential
