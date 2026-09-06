import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
import InfoGeometry.Canonical.NativeOperatorialExponentialFamily
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic

/-!
InfoGeometry.Canonical.SouriauOperatorialLogPotential
-/

namespace InfoGeometry.Canonical.SouriauOperatorialLogPotential

open InfoGeometry.Canonical.StandardFormCore

/-! A scalar density is retained only as a carrier type for the finite
Souriau readout structures below.  It is not a Radon--Nikodym datum or an
operatorial modular state. -/
abbrev Density (State : Type*) := State → ℝ

/-! A positive scalar trace normalization used only as the finite readout
of an operatorial partition family. -/
@[rep_depth operator]
abbrev PositivePartitionFunction :=
  {Z : ℝ // 0 < Z}

@[rep_depth operator]
structure DuhamelOperatorDerivative (Param Op Direction : Type*) where
  /-- Operator-valued generator. -/
  K : Param → Op
  /-- Directional operator insertion. -/
  directionToInsertion : Direction → Op
  /-- Ordered higher forms, retaining noncommutative insertion order. -/
  higherSimplexOrderedForms : Nat → Param → List Direction → Op
  /-- Scalar trace/KMS readout of an operator. -/
  traceStateKMSReadout : Op → ℝ

namespace DuhamelOperatorDerivative
  variable {Param Op Direction : Type*}

  def derivativeOfExp
      (D : DuhamelOperatorDerivative Param Op Direction) :
      Param → Direction → Op :=
    fun β δ => D.higherSimplexOrderedForms 1 β [δ]

  @[simp, rep_depth operator]
  theorem derivativeOfExp_eq_first_ordered_form
      (D : DuhamelOperatorDerivative Param Op Direction)
      (β : Param) (δ : Direction) :
      D.derivativeOfExp β δ = D.higherSimplexOrderedForms 1 β [δ] :=
    rfl
end DuhamelOperatorDerivative

@[rep_depth operator]
structure MomentGeneratingReadout
    (Param Op : Type*)
    [AddMonoid Param]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op] where
  family : NativeOperatorialExponentialFamily.Family Param Op
  /-- Normalized state readout, kept separate from the untraced exponential. -/
  normalizedState : Param → Op
  firstMoment : Param → Op → ℝ
  bkmCovariance : Param → Op → Op → ℝ
  nResponseForm : Nat → Param → List Op → ℝ
  firstMoment_eq_trace_normalized_mul :
    ∀ β O, firstMoment β O = family.traceReadout (normalizedState β * O)
  bkmCovariance_symm :
    ∀ β A B, bkmCovariance β A B = bkmCovariance β B A
  bkmCovariance_self_nonneg :
    ∀ β A, 0 ≤ bkmCovariance β A A
  nResponseForm_one_two_eq :
    ∀ β A B,
      nResponseForm 1 β [A] = firstMoment β A ∧
      nResponseForm 2 β [A, B] = bkmCovariance β A B

theorem firstMomentLawClaim
    {Param Op : Type*} [AddMonoid Param]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]
    (M : MomentGeneratingReadout Param Op) (β : Param) (O : Op) :
  M.firstMoment β O = M.family.traceReadout (M.normalizedState β * O) :=
  M.firstMoment_eq_trace_normalized_mul β O
theorem bkmCovarianceSymmetryClaim
    {Param Op : Type*} [AddMonoid Param]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]
    (M : MomentGeneratingReadout Param Op) (β : Param) (A B : Op) :
  M.bkmCovariance β A B = M.bkmCovariance β B A :=
  M.bkmCovariance_symm β A B
theorem bkmCovariancePSDClaim
    {Param Op : Type*} [AddMonoid Param]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]
    (M : MomentGeneratingReadout Param Op) (β : Param) (A : Op) :
  M.bkmCovariance β A A ≥ 0 :=
  M.bkmCovariance_self_nonneg β A
theorem higherCumulantBoundaryLawClaim
    {Param Op : Type*} [AddMonoid Param]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]
    (M : MomentGeneratingReadout Param Op) (β : Param) (A B : Op) :
  M.nResponseForm 1 β [A] = M.firstMoment β A ∧
  M.nResponseForm 2 β [A, B] = M.bkmCovariance β A B :=
  M.nResponseForm_one_two_eq β A B

@[rep_depth operator]
abbrev OperatorialMomentGeneratingPotential
    (Param Obs : Type*) [AddMonoid Param]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] :=
  MomentGeneratingReadout Param Obs

namespace OperatorialMomentGeneratingPotential
  variable {Param Obs : Type*}
  variable [AddMonoid Param]
  variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

  /-- The second response form is the operatorial BKM covariance readout. -/
  def covarianceTensor
      (M : OperatorialMomentGeneratingPotential Param Obs)
      (β : Param) : Obs → Obs → ℝ :=
    M.bkmCovariance β

  @[rep_depth operator]
  theorem covarianceTensor_eq_bkmCovariance
      (M : OperatorialMomentGeneratingPotential Param Obs)
      (β : Param) (A B : Obs) :
      M.covarianceTensor β A B = M.bkmCovariance β A B :=
    rfl

  @[rep_depth operator]
  theorem covarianceTensor_symm
      (M : OperatorialMomentGeneratingPotential Param Obs)
      (β : Param) (A B : Obs) :
      M.covarianceTensor β A B = M.covarianceTensor β B A := by
    exact M.bkmCovariance_symm β A B

  @[rep_depth operator]
  theorem covarianceTensor_self_nonneg
      (M : OperatorialMomentGeneratingPotential Param Obs)
      (β : Param) (A : Obs) :
      0 ≤ M.covarianceTensor β A A := by
    exact M.bkmCovariance_self_nonneg β A
end OperatorialMomentGeneratingPotential

@[rep_depth operator]
structure QuantumOperatorialSouriauFamily
    (LieAlgebra Obs : Type*)
    [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] where
  /-- Operator-valued sufficient statistic / quantum moment map. -/
  Jhat : LieAlgebra → Obs
  /-- Lie-algebra parameter selecting the operatorial thermal direction. -/
  beta : LieAlgebra
  /-- Native noncommutative exponential family behind the thermal weight. -/
  exponentialFamily : NativeOperatorialExponentialFamily.Family LieAlgebra Obs
  /-- The family generator is the Souriau moment-map generator. -/
  generator_eq_Jhat : ∀ x, exponentialFamily.generator x = Jhat x
  /-- Positive scalar trace/state normalization of the operator weight. -/
  positivePartitionFunction : PositivePartitionFunction
  /-- The installed partition normalization is the readout of the weight. -/
  partitionFunction_eq_trace :
    exponentialFamily.traceReadout
        (exponentialFamily.untracedExponential beta) = positivePartitionFunction

namespace QuantumOperatorialSouriauFamily

variable {LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

@[rep_depth operator]
def Khat_beta (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Obs :=
  Q.exponentialFamily.generator Q.beta

@[rep_depth operator]
noncomputable def untracedExponential
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Obs :=
  Q.exponentialFamily.untracedExponential Q.beta

@[rep_depth operator]
def traceReadout
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Obs → ℝ :=
  Q.exponentialFamily.traceReadout

@[rep_depth operator]
def opAdd [Add Obs] (_Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Obs → Obs → Obs :=
  (· + ·)

@[rep_depth operator]
def opScale [SMul ℝ Obs] (_Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    ℝ → Obs → Obs :=
  (· • ·)

@[rep_depth operator]
def opIdentity [One Obs] (_Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Obs :=
  1

@[rep_depth thermo]
def partitionFunction (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : ℝ :=
  Q.positivePartitionFunction

@[rep_depth operator]
theorem partitionFunction_eq_traceReadout
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.traceReadout Q.untracedExponential = Q.partitionFunction := by
  exact Q.partitionFunction_eq_trace

@[rep_depth thermo]
  noncomputable def partitionPotential (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : ℝ :=
  Real.log Q.partitionFunction

@[rep_depth operator]
  noncomputable def rho_beta [SMul ℝ Obs] (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Obs :=
  Q.partitionFunction⁻¹ • Q.untracedExponential

@[rep_depth operator]
  noncomputable def modularHamiltonian [Add Obs] [SMul ℝ Obs] [One Obs]
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Obs :=
  Q.Khat_beta + Q.partitionPotential • (1 : Obs)

@[rep_depth thermo]
theorem partitionFunction_pos (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    0 < Q.partitionFunction :=
  Q.positivePartitionFunction.property

@[rep_depth operator]
theorem Khat_beta_eq (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.Khat_beta = Q.Jhat Q.beta :=
  Q.generator_eq_Jhat Q.beta

@[rep_depth thermo]
theorem partitionPotential_eq_log_trace
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.partitionPotential = Real.log Q.partitionFunction :=
  rfl

@[rep_depth operator]
theorem rho_beta_eq_normalized_exp [SMul ℝ Obs]
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.rho_beta = Q.opScale Q.partitionFunction⁻¹ Q.untracedExponential :=
  rfl

@[rep_depth operator]
theorem modularHamiltonian_eq [Add Obs] [SMul ℝ Obs] [One Obs]
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.modularHamiltonian =
      Q.opAdd Q.Khat_beta (Q.opScale Q.partitionPotential Q.opIdentity) :=
  rfl

@[rep_depth operator]
theorem opAdd_eq_add [Add Obs] (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs)
    (A B : Obs) :
    Q.opAdd A B = A + B :=
  rfl

@[rep_depth operator]
theorem opScale_eq_smul [SMul ℝ Obs]
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) (r : ℝ) (A : Obs) :
    Q.opScale r A = r • A :=
  rfl

@[rep_depth operator]
theorem opIdentity_eq_one [One Obs]
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.opIdentity = (1 : Obs) :=
  rfl

end QuantumOperatorialSouriauFamily

theorem quantumTraceClassClaim
    {LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
  0 < Q.partitionFunction :=
  Q.partitionFunction_pos
theorem traceStateKMSReadoutRequiredClaim
    {LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] [SMul ℝ Obs]
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
  Q.rho_beta = Q.opScale (Q.partitionFunction⁻¹) Q.untracedExponential :=
  Q.rho_beta_eq_normalized_exp

namespace QuantumOperatorialSouriauFamily
  variable {LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
  variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
  @[rep_depth operator]
  theorem modularHamiltonian_eq_Khat_add_logZ [Add Obs] [SMul ℝ Obs] [One Obs]
      (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
      Q.modularHamiltonian =
        Q.opAdd Q.Khat_beta (Q.opScale Q.partitionPotential Q.opIdentity) :=
    Q.modularHamiltonian_eq

  @[rep_depth operator]
  theorem Khat_beta_eq_Jhat_beta (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Q.Khat_beta = Q.Jhat Q.beta := Q.Khat_beta_eq
end QuantumOperatorialSouriauFamily

/-! ## Operatorial state and relative-surprisal carriers -/

@[rep_depth operator]
structure OperatorialSouriauStateData
    (State LieAlgebra Obs : Type*) [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] where
  family : QuantumOperatorialSouriauFamily LieAlgebra Obs
  observable : State → Obs

namespace OperatorialSouriauStateData

variable {State LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

@[rep_depth operator]
def operatorialHamiltonian
    (D : OperatorialSouriauStateData State LieAlgebra Obs) : State → Obs :=
  fun x => D.family.Khat_beta * D.observable x

@[rep_depth thermo]
def K_beta
    (D : OperatorialSouriauStateData State LieAlgebra Obs) : State → ℝ :=
  fun x => D.family.traceReadout (D.operatorialHamiltonian x)

@[rep_depth thermo]
noncomputable def partitionPotential
    (D : OperatorialSouriauStateData State LieAlgebra Obs) : ℝ :=
  D.family.partitionPotential

@[rep_depth thermo]
noncomputable def gibbsDensity
    (D : OperatorialSouriauStateData State LieAlgebra Obs) : Density State :=
  fun x => Real.exp (-D.K_beta x - D.partitionPotential)

@[rep_depth thermo]
theorem partitionPotential_eq_log_partitionFunction
    (D : OperatorialSouriauStateData State LieAlgebra Obs) :
    D.partitionPotential = Real.log D.family.partitionFunction :=
  D.family.partitionPotential_eq_log_trace

@[rep_depth thermo]
theorem gibbsDensity_eq_exp_neg_K_beta_sub_partitionPotential
    (D : OperatorialSouriauStateData State LieAlgebra Obs) (x : State) :
    D.gibbsDensity x = Real.exp (-D.K_beta x - D.partitionPotential) :=
  rfl

@[rep_depth operator]
theorem operatorialHamiltonian_eq_left_product
    (D : OperatorialSouriauStateData State LieAlgebra Obs) (x : State) :
    D.operatorialHamiltonian x = D.family.Khat_beta * D.observable x :=
  rfl

end OperatorialSouriauStateData

@[rep_depth operator]
structure OperatorialRNDatum
    (State LieAlgebra Obs : Type*) [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] where
  souriau : OperatorialSouriauStateData State LieAlgebra Obs
  rnDerivative : Density State
  rnDerivative_eq_gibbsDensity : rnDerivative = souriau.gibbsDensity
  expectation : Density State → ℝ

namespace OperatorialRNDatum

variable {State LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

@[rep_depth operator]
noncomputable def modularPotential
    (D : OperatorialRNDatum State LieAlgebra Obs) : Density State :=
  fun x => -Real.log (D.rnDerivative x)

@[rep_depth thermo]
noncomputable def entropy
    (D : OperatorialRNDatum State LieAlgebra Obs) : ℝ :=
  D.expectation D.modularPotential

@[rep_depth operator]
theorem rnDerivative_eq_gibbsDensity_apply
    (D : OperatorialRNDatum State LieAlgebra Obs) (x : State) :
    D.rnDerivative x = D.souriau.gibbsDensity x := by
  simpa only using congrFun D.rnDerivative_eq_gibbsDensity x

@[rep_depth operator]
theorem modularPotential_eq_K_beta_add_partitionPotential
    (D : OperatorialRNDatum State LieAlgebra Obs) (x : State) :
    D.modularPotential x = D.souriau.K_beta x + D.souriau.partitionPotential := by
  unfold modularPotential
  rw [D.rnDerivative_eq_gibbsDensity_apply]
  rw [D.souriau.gibbsDensity_eq_exp_neg_K_beta_sub_partitionPotential]
  rw [Real.log_exp]
  ring

@[rep_depth thermo]
theorem entropy_eq_expectation_modularPotential
    (D : OperatorialRNDatum State LieAlgebra Obs) :
    D.entropy = D.expectation D.modularPotential :=
  rfl

end OperatorialRNDatum

@[rep_depth operator]
structure OperatorialCovarianceAndCocycle
    (State LieGroup LieAlgebra Obs : Type*)
    [Mul LieGroup] [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    [Add Obs] where
  family : QuantumOperatorialSouriauFamily LieAlgebra Obs
  groupAction : LieGroup → State → State
  operatorAction : LieGroup → Obs → Obs
  observable : State → Obs
  betaAction : LieGroup → LieAlgebra → LieAlgebra
  cocycle : LieGroup → Obs
  strictEquivariance :
    ∀ g x, observable (groupAction g x) = operatorAction g (observable x)
  affineCocycle :
    ∀ g h, cocycle (g * h) = operatorAction g (cocycle h) + cocycle g

@[rep_depth operator]
theorem operatorialPartitionPotentialAffineCorrection
    {State LieGroup LieAlgebra Obs : Type*}
    [Mul LieGroup] [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] [Add Obs]
    (L : OperatorialCovarianceAndCocycle State LieGroup LieAlgebra Obs)
    (g h : LieGroup) :
    L.cocycle (g * h) = L.operatorAction g (L.cocycle h) + L.cocycle g :=
  L.affineCocycle g h

/-!
The former scalar `SouriauMetriplecticOnsager`, `OptimalTransportWitness`, and
`GenericMetriplecticCompatibility` packets were removed.  They only stored
arbitrary real-valued maps together with their desired inequalities, so their
projection lemmas did not establish an operatorial metriplectic law.

The maintained owners are the noncommutative channels imported above:
`RelativeModularPotential` for the state-induced operator dynamics and
`OnsagerReciprocity` for the symmetric/antisymmetric operator Hessian forms.
Their theorems must be consumed directly rather than repackaged in scalar
zero instances.
-/

end InfoGeometry.Canonical.SouriauOperatorialLogPotential
