import InfoGeometry.LLM.RouterFreeEnergyBridge
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace KMSSoftmaxBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.LLM.RouterFreeEnergyBridge

section TokenLocalKMS

variable {Tok V : Type*}
variable [NormedAddCommGroup V]

/-- Softmax router weight (token-local expert lane). -/
noncomputable def softmaxWeight
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  normalizedWeights n β x i e

/-- Same weight viewed through finite-diagonal KMS/Gibbs semantics. -/
noncomputable def kmsWeight
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  InfoGeometry.Thermo.FiniteDiagonal.gibbsWeight (routerHamiltonian n x i) β e

/-- Router logit on the token-local expert lane (`-β H`). -/
noncomputable def routerLogit
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) : ℝ :=
  -β * routerHamiltonian n x i e

/-- Softmax weights are exactly KMS/Gibbs weights on the router Hamiltonian. -/
@[simp, rep_depth transport]
theorem softmaxWeight_eq_kmsWeight
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    softmaxWeight n β x i e = kmsWeight n β x i e := by
  exact normalizedWeights_eq_finite_gibbsWeight (n := n) (β := β) (x := x) (i := i) (e := e)

/-- Explicit softmax form on router logits: `exp(logit) / Z`. -/
@[simp, rep_depth transport]
theorem softmaxWeight_eq_exp_routerLogit_div_partition
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    softmaxWeight n β x i e
      = Real.exp (routerLogit n β x i e) / routerPartition n β x i := by
  simp [softmaxWeight, routerLogit, normalizedWeights, unnormalizedWeights, routerHamiltonian]

/-- Finite KMS normalization on each token-local expert slice. -/
@[simp, rep_depth transport]
theorem kmsWeight_sum_one
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : ExpertIdx n, kmsWeight n β x i e = 1 := by
  unfold kmsWeight
  simpa using
    (InfoGeometry.Thermo.FiniteDiagonal.gibbsWeight_sum_one
      (H := routerHamiltonian n x i) (β := β))

/-- Softmax normalization coincides with finite KMS normalization (`∑ᵢ wᵢ = 1`). -/
@[simp, rep_depth transport]
theorem softmaxWeight_sum_one
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : ExpertIdx n, softmaxWeight n β x i e = 1 := by
  simpa [softmaxWeight] using
    (normalizedWeights_sum_one (n := n) β x i)

/-- KMS log-partition surface on the token-local router slice. -/
noncomputable def kmsLogPartition
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) : ℝ :=
  routerMassieu n β x i

/-- KMS log-partition matches the router log-sum-exp surface. -/
@[simp, rep_depth transport]
theorem kmsLogPartition_eq_logSumExpRouter
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) :
    kmsLogPartition n β x i
      = InfoGeometry.LLM.ThermodynamicSwitching.logSumExpRouter (n := n) β x i := by
  exact routerMassieu_eq_logSumExpRouter (n := n) (β := β) (x := x) (i := i)

/-- KMS entropy decomposition on the router slice: `S = β U + ψ`. -/
@[rep_depth transport]
theorem kmsEntropy_eq_beta_internal_plus_logPartition
    (n : Nat) [Nonempty (Fin n)] (β : ℝ) (x : Tok → V) (i : Tok) :
    routerEntropy n β x i
      = β * routerInternalEnergy n β x i + kmsLogPartition n β x i := by
  simpa [kmsLogPartition] using
    (routerEntropy_eq_beta_internal_plus_massieu (n := n) (β := β) (x := x) (i := i))

/-- KMS free-energy relation: `β F = -ψ` for nonzero inverse temperature. -/
@[rep_depth transport]
theorem beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    β * routerFreeEnergy n β x i = -kmsLogPartition n β x i := by
  simpa [kmsLogPartition] using
    (beta_mul_routerFreeEnergy_eq_neg_routerMassieu
      (n := n) (β := β) (x := x) (i := i) hβ)

/-- Temperature-regularized free energy identity under `β = 1/ε`. -/
@[rep_depth transport]
theorem routerFreeEnergyEps_eq_neg_eps_kmsLogPartition
    (n : Nat) [Nonempty (Fin n)]
    (ε : ℝ) (x : Tok → V) (i : Tok) (hε : ε ≠ 0) :
    routerFreeEnergyEps n ε x i
      = -ε * kmsLogPartition n (1 / ε) x i := by
  have h :=
    routerFreeEnergyEps_eq_neg_eps_logSumExpRouter
      (n := n) (ε := ε) (x := x) (i := i) hε
  simpa [kmsLogPartition_eq_logSumExpRouter (n := n) (β := 1 / ε) (x := x) (i := i)] using h

end TokenLocalKMS

end KMSSoftmaxBridge
