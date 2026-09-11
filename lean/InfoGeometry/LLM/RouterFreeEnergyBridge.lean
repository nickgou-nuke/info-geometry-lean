import InfoGeometry.LLM.ThermodynamicSwitching
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermo.ThermodynamicIdentities
import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM.RouterFreeEnergyBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Thermo.FiniteDiagonal

section TokenLocalThermo

variable {Tok V : Type*}
variable [NormedAddCommGroup V]

/-- Token-local Hamiltonian over experts induced by router energy. -/
def routerHamiltonian (n : Nat) (x : Tok → V) (i : Tok) : Fin n → ℝ :=
  routerEnergy n x i

/-- Router partition is exactly the finite diagonal thermal partition. -/
@[rep_depth transport]
theorem routerPartition_eq_finitePartition
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) :
    routerPartition n β x i
      = partition (routerHamiltonian n x i) β := by
  rfl

/-- Router normalized weights coincide with finite-diagonal Gibbs weights. -/
@[rep_depth transport]
theorem normalizedWeights_eq_finite_gibbsWeight
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    normalizedWeights n β x i e
      = gibbsWeight (routerHamiltonian n x i) β e := by
  rfl

/-- Token-local internal energy from the router Hamiltonian. -/
noncomputable def routerInternalEnergy
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  InfoGeometry.Thermo.FiniteDiagonal.internalEnergy (routerHamiltonian n x i) β

/-- Token-local entropy from the router Hamiltonian. -/
noncomputable def routerEntropy
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  InfoGeometry.Thermo.FiniteDiagonal.entropy (routerHamiltonian n x i) β

/-- Token-local Massieu potential from the router Hamiltonian. -/
noncomputable def routerMassieu
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  InfoGeometry.Thermo.FiniteDiagonal.massieu (routerHamiltonian n x i) β

/-- Token-local free energy from the router Hamiltonian. -/
noncomputable def routerFreeEnergy
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  InfoGeometry.Thermo.FiniteDiagonal.freeEnergy (routerHamiltonian n x i) β

/-- Router Massieu potential is exactly the router log-sum-exp partition surface. -/
@[rep_depth transport]
theorem routerMassieu_eq_logSumExpRouter
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) :
    routerMassieu n β x i
      = InfoGeometry.LLM.ThermodynamicSwitching.logSumExpRouter (n := n) β x i := by
  unfold routerMassieu InfoGeometry.LLM.ThermodynamicSwitching.logSumExpRouter massieu
  rw [routerPartition_eq_finitePartition n β x i]

/-- Router entropy decomposition: `S = β U + ψ` on each token-local expert slice. -/
@[rep_depth transport]
theorem routerEntropy_eq_beta_internal_plus_massieu
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) :
    routerEntropy n β x i = β * routerInternalEnergy n β x i + routerMassieu n β x i := by
  simpa [routerEntropy, routerInternalEnergy, routerMassieu, routerHamiltonian] using
    (entropy_eq_beta_internal_plus_massieu (H := routerHamiltonian n x i) (β := β))

/-- Router free-energy identity: `β F = -ψ` for nonzero inverse temperature. -/
@[rep_depth transport]
theorem beta_mul_routerFreeEnergy_eq_neg_routerMassieu
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    β * routerFreeEnergy n β x i = -routerMassieu n β x i := by
  simpa [routerFreeEnergy, routerMassieu, routerHamiltonian] using
    (beta_mul_freeEnergy (H := routerHamiltonian n x i) (β := β) hβ)

/-- Temperature-regularized router free energy under `β = 1/ε`. -/
noncomputable def routerFreeEnergyEps
    (n : Nat) [Nonempty (Fin n)] (ε : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  routerFreeEnergy n (1 / ε) x i

/-- Under `β = 1/ε`, free energy is `-ε * log Z` on the router slice. -/
@[rep_depth transport]
theorem routerFreeEnergyEps_eq_neg_eps_logSumExpRouter
    (n : Nat) [Nonempty (Fin n)]
    (ε : ℝ) (x : Tok → V) (i : Tok) (hε : ε ≠ 0) :
    routerFreeEnergyEps n ε x i
      = -ε * InfoGeometry.LLM.ThermodynamicSwitching.logSumExpRouter (n := n) (1 / ε) x i := by
  unfold routerFreeEnergyEps routerFreeEnergy InfoGeometry.Thermo.FiniteDiagonal.freeEnergy
  have hdiv : (1 / (1 / ε)) = ε := by
    field_simp [hε]
  rw [hdiv]
  have hM := routerMassieu_eq_logSumExpRouter n (1 / ε) x i
  simpa [routerMassieu] using congrArg (fun t => -ε * t) hM

end TokenLocalThermo

section ScaledEntropicBridge

variable {Tok V : Type*}
variable [NormedAddCommGroup V]

/-- Router-scaled entropic objective (KL side) in the analytic log-sum-exp family. -/
noncomputable def routerScaledEntropicObjective
    (n : Nat) [Nonempty (Fin n)]
    (ε θ η : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  InfoGeometry.Analytic.logSumExpScaledEntropicTransportObjective
    (w := fun _ : ExpertIdx n => (1 : ℝ))
    (a := fun e => -routerEnergy n x i e)
    ε θ η

/-- Router-scaled convex potential gap (Bregman side) in the analytic log-sum-exp family. -/
noncomputable def routerScaledPotentialGap
    (n : Nat) [Nonempty (Fin n)]
    (ε θ η : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  InfoGeometry.Analytic.logSumExpScaledEntropicTransportPotentialGap
    (w := fun _ : ExpertIdx n => (1 : ℝ))
    (a := fun e => -routerEnergy n x i e)
    ε θ η

@[simp, rep_depth transport]
theorem routerScaledEntropicObjective_eq_scaledKL
    (n : Nat) [Nonempty (Fin n)]
    (ε θ η : ℝ) (x : Tok → V) (i : Tok) :
    routerScaledEntropicObjective n ε θ η x i
      = InfoGeometry.Analytic.logSumExpScaledKL
          (w := fun _ : ExpertIdx n => (1 : ℝ))
          (a := fun e => -routerEnergy n x i e)
          ε θ η := by
  unfold routerScaledEntropicObjective
  exact InfoGeometry.Analytic.logSumExpScaledEntropicTransportObjective_eq
      (w := fun _ : ExpertIdx n => (1 : ℝ))
      (a := fun e => -routerEnergy n x i e)
      ε θ η

@[simp, rep_depth transport]
theorem routerScaledPotentialGap_eq_scaledBregman_swapped
    (n : Nat) [Nonempty (Fin n)]
    (ε θ η : ℝ) (x : Tok → V) (i : Tok) :
    routerScaledPotentialGap n ε θ η x i
      = InfoGeometry.Analytic.logSumExpScaledBregman
          (w := fun _ : ExpertIdx n => (1 : ℝ))
          (a := fun e => -routerEnergy n x i e)
          ε η θ := by
  unfold routerScaledPotentialGap
  exact InfoGeometry.Analytic.logSumExpScaledEntropicTransportPotentialGap_eq
      (w := fun _ : ExpertIdx n => (1 : ℝ))
      (a := fun e => -routerEnergy n x i e)
      ε θ η

/--
Compatibility alias.

Note the argument order on the Bregman side is intentionally `(ε, η, θ)`,
while the potential-gap side is parameterized as `(ε, θ, η)`.
-/
@[simp, rep_depth transport]
theorem routerScaledPotentialGap_eq_scaledBregman
    (n : Nat) [Nonempty (Fin n)]
    (ε θ η : ℝ) (x : Tok → V) (i : Tok) :
    routerScaledPotentialGap n ε θ η x i
      = InfoGeometry.Analytic.logSumExpScaledBregman
          (w := fun _ : ExpertIdx n => (1 : ℝ))
          (a := fun e => -routerEnergy n x i e)
          ε η θ :=
  routerScaledPotentialGap_eq_scaledBregman_swapped (n := n) (ε := ε) (θ := θ) (η := η) (x := x) (i := i)

end ScaledEntropicBridge

end InfoGeometry.LLM.RouterFreeEnergyBridge
