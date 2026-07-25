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
  /-- Statewise Boltzmann entropy: `S_B(x) = -log ρ(x)`.
  This is the **modular Hamiltonian** in AQFT / Connes-Tomita-Takesaki theory.
  It is a function on microstates, NOT an ensemble average. -/
  noncomputable def boltzmannEntropy (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : Density State :=
    fun x => -Real.log (D.rnDerivative x)

  /-- The modular Hamiltonian IS the Boltzmann entropy operator.
  By definition: `K_β(x) = -log ρ_β(x)`.
  In the canonical ensemble, `ρ_β(x) = e^{-βH(x)}/Z` so `K_β(x) = βH(x) + log Z`. -/
  noncomputable def modularHamiltonian (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : Density State :=
    D.boltzmannEntropy

  /-- Gibbs / von Neumann ensemble entropy: `S_G = ⟨-log ρ⟩ = ∫ ρ(x)(-log ρ(x)) dx`.
  This is the EXPECTATION of the Boltzmann entropy, not the Boltzmann entropy itself. -/
  @[rep_depth thermo]
  noncomputable def gibbsEntropy (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : ℝ :=
    D.expectationBeta D.boltzmannEntropy

  /-- The statewise modular Hamiltonian equals `K_β + Φ` (from Souriau structure). -/
  @[rep_depth thermo]
  theorem rnDerivative_eq_gibbsDensity_apply (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) : D.rnDerivative x = D.souriau.gibbsDensity x := by
    simpa only using congrFun D.rnDerivative_eq_gibbsDensity x

  @[rep_depth thermo]
  theorem modularHamiltonian_eq_K_beta_add_Phi (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) : D.modularHamiltonian x = D.souriau.K_beta x + D.souriau.partitionPotential := by
    have h₁ : D.modularHamiltonian x = D.boltzmannEntropy x := rfl
    rw [h₁]
    have h₂ : D.boltzmannEntropy x = -Real.log (D.rnDerivative x) := rfl
    rw [h₂]
    have h₃ : -Real.log (D.rnDerivative x) = -Real.log (D.souriau.gibbsDensity x) := by
      rw [rnDerivative_eq_gibbsDensity_apply D x]
    rw [h₃]
    exact D.souriau.negativeLogGibbsDensity_eq_K_beta_add_Phi x

  /-- Gibbs entropy is the expectation of the Boltzmann entropy: `S_G = ⟨S_B⟩`. -/
  @[rep_depth thermo]
  theorem gibbsEntropy_eq_expectation_boltzmannEntropy (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : D.gibbsEntropy = D.expectationBeta D.boltzmannEntropy := rfl

  @[rep_depth thermo]
  theorem entropy_eq_Phi_add_pairing_Q_beta (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : D.gibbsEntropy = D.souriau.partitionPotential + D.souriau.pairing D.Q D.souriau.beta := by
    simpa [gibbsEntropy, boltzmannEntropy] using D.entropy_eq_Phi_add_pairing_Q_beta
end SouriauNegativeLogRNDerivative

def instSouriauNegativeLogRNDerivative : SouriauNegativeLogRNDerivative Unit Unit Unit where
  souriau := instSouriauLieThermoData
  rnDerivative _ := 1
  rnDerivative_eq_gibbsDensity := rfl
  expectationBeta _ := 0
  Q := ()
  entropy_eq_Phi_add_pairing_Q_beta := by change (0 : ℝ) = 0 + 0; norm_num
/-- The modular Hamiltonian IS the negative log density operator = Boltzmann entropy operator / log-generating operator. The historical name "modular Hamiltonian" is unfortunate; it is the log-generating operator for the Boltzmann Gibbs state. -/
theorem modularHamiltonian_is_negativeLogDensity {Op : Type*} [Module ℝ Op] (M : ModularHamiltonianData Op) : M.modularHamiltonian = M.negativeLogDensity := rfl

/-- The modular potential IS the negative log Radon-Nikodym derivative = Boltzmann entropy operator. -/
theorem modularPotential_is_negLogRN (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) : D.modularPotential x = -Real.log (D.rnDerivative x) := rfl

/-- The entropy IS the expectation of the Boltzmann entropy operator (modular Hamiltonian). -/
theorem entropy_is_expectation_of_BoltzmannEntropy (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) : D.entropy = D.expectationBeta D.modularPotential := rfl

/-- The modular Hamiltonian in the quantum operatorial family IS the operatorial Boltzmann entropy operator: K̂_β + ln Z · I. -/
theorem modularHamiltonian_is_BoltzmannEntropyOperator {LieAlgebra Obs : Type*} (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) : Q.modularHamiltonian = Q.opAdd Q.Khat_beta (Q.opScale Q.partitionPotential Q.opIdentity) := rfl
