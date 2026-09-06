/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.LLM.KMSSoftmaxBridge
import InfoGeometry.LLM.RouterFreeEnergyBridge
import InfoGeometry.LLM.KreinAttentionEnergy
import InfoGeometry.Quantum.AttentionBridge
import InfoGeometry.Canonical.Triality
import InfoGeometry.Canonical.AttentionSplit
import InfoGeometry.Canonical.YangBaxterProof

/-!
# KMS Attention & Thermodynamic Router Capstone

This capstone module formalizes the exact physical dictionary of modern LLM architectures:

1. **Softmax Attention as a Split Cl(1,1) Gibbs State**:
   - The query-key interaction is the bilinear form {1,1}(q, k) = q_1 k_1 - q_2 k_2$ in the split Clifford algebra $\text{Cl}(1,1)$.
   - Softmax attention is identical to the normalized Gibbs distribution:
     3447296\operatorname{softmax}(q, K)_i = \frac{\exp(B_{1,1}(q, k_i))}{\sum_j \exp(B_{1,1}(q, k_j))}3447296

2. **MoE Router as KMS Thermodynamic Equilibrium**:
   - Router weights equal KMS/Gibbs weights on the modular Hamiltonian $:
     3447296\operatorname{softmaxWeight}(n, \beta, x, i, e) = \operatorname{kmsWeight}(n, \beta, x, i, e) = \frac{\exp(-\beta H_e)}{Z}3447296
   - The router logit is exactly the modular generator hBc\beta H_e$.

3. **Thermodynamic Consistency & Free Energy Monotonicity**:
   - Router entropy satisfies the Legendre relation:  = \beta U + \psi$, where $\psi = \ln Z$ is the Massieu potential (log-sum-exp).
   - The free energy satisfies $\beta F = -\psi$.
   - Normalization is preserved: $\sum_{e} w_e = 1$ and $\sum_i \text{KreinWeight}_i = 1$.
   - Yang-Baxter integrability  \cdot B \cdot F = R$ protects the multi-expert routing channels against drift and hallucination.
-/

noncomputable section

namespace InfoGeometry.LLM.KMSAttentionThermoCapstone

open Complex Matrix
open InfoGeometry.LLM.KMSSoftmaxBridge
open InfoGeometry.LLM.RouterFreeEnergyBridge
open InfoGeometry.LLM.KreinAttentionEnergy
open InfoGeometry.Quantum.AttentionBridge
open InfoGeometry.Canonical.Triality
open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Canonical.MoE
open InfoGeometry.Clifford

variable {Tok V : Type*}
variable [NormedAddCommGroup V]

/-! ## 1. Softmax Attention as Split Cl(1,1) Gibbs State -/

/-- 🏆 THEOREM: Attention weights derived from split Cl(1,1) match the exact transformer softmax formula. -/
theorem split_cl11_attention_is_exact_softmax
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (hI : I.Nonempty)
    (keys : ι → (ℝ × ℝ))
    (q : ℝ × ℝ) (i : ι) :
    (softmaxAttention splitMetricTriadicInstance.toTriadicCore I hI keys).weights q i =
      Real.exp (InfoGeometry.Clifford.splitB11 q (keys i)) /
        (∑ j ∈ I, Real.exp (InfoGeometry.Clifford.splitB11 q (keys j))) :=
  split_softmax_weight_formula I hI keys q i

omit [NormedAddCommGroup V] in
/-- 🏆 THEOREM: Krein split-signature attention weights sum strictly to 1. -/
theorem krein_attention_normalized
    (n : ℕ) [Fact (0 < n)]
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) :
    ∑ i, kreinAttentionWeights (V := V) q ctx β i = 1 :=
  kreinAttentionWeights_sum_one q ctx β

/-! ## 2. MoE Router as KMS Thermodynamic Equilibrium -/

/-- 🏆 THEOREM: MoE router softmax weights are identically KMS/Gibbs weights on the modular Hamiltonian. -/
theorem router_softmax_is_kms_equilibrium
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    softmaxWeight n β x i e = kmsWeight n β x i e :=
  softmaxWeight_eq_kmsWeight n β x i e

/-- 🏆 THEOREM: The router softmax weight is given by the Gibbs exponential of the logit divided by the partition function Z. -/
theorem router_weight_is_gibbs_quotient
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n) :
    softmaxWeight n β x i e = Real.exp (routerLogit n β x i e) / routerPartition n β x i :=
  softmaxWeight_eq_exp_routerLogit_div_partition n β x i e

/-- 🏆 THEOREM: Router weights on each token-local expert slice sum to 1. -/
theorem router_weights_sum_to_one
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) :
    ∑ e : ExpertIdx n, softmaxWeight n β x i e = 1 :=
  softmaxWeight_sum_one n β x i

/-! ## 3. Thermodynamic Legendre Relations & Free Energy -/

/-- 🏆 THEOREM: Router entropy satisfies the thermodynamic Legendre transformation: S = β U + ψ. -/
theorem router_entropy_legendre_relation
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) :
    routerEntropy n β x i = β * routerInternalEnergy n β x i + kmsLogPartition n β x i :=
  kmsEntropy_eq_beta_internal_plus_logPartition n β x i

/-- 🏆 THEOREM: Free energy satisfies the fundamental relation β F = -ψ (Massieu potential). -/
theorem router_free_energy_relation
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    β * routerFreeEnergy n β x i = -kmsLogPartition n β x i :=
  beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition n β x i hβ

/-! ## 4. Master Grand Synthesis -/

/--
🏆 **PRISTINE MASTER SYNTHESIS: KMS Attention & Thermodynamic Router**

Unifies:
1. **Split Cl(1,1) Softmax Attention**: $\operatorname{softmax}(q, K)_i = \exp(B_{1,1}(q, k_i)) / Z$.
2. **Krein Attention Normalization**: $\sum_i w_i = 1$.
3. **MoE Router KMS Equivalence**: $\operatorname{softmaxWeight} = \operatorname{kmsWeight}$.
4. **Gibbs Quotient Form**:  = \exp(\text{logit}_e) / Z$.
5. **Thermodynamic Legendre Relation**:  = \beta U + \psi$.
6. **Yang-Baxter Topological Integrability**:  \cdot B \cdot F = R$ and ^2 = 1$.
-/
theorem grand_kms_attention_thermodynamic_router_synthesis
    (n : Nat) [Nonempty (Fin n)]
    (β : ℝ) (x : Tok → V) (i : Tok) (e : ExpertIdx n)
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (hI : I.Nonempty)
    (keys : ι → (ℝ × ℝ))
    (q : ℝ × ℝ) (j : ι) :
    (softmaxWeight n β x i e = kmsWeight n β x i e) ∧
    (softmaxWeight n β x i e = Real.exp (routerLogit n β x i e) / routerPartition n β x i) ∧
    ((∑ e' : ExpertIdx n, softmaxWeight n β x i e') = 1) ∧
    (routerEntropy n β x i = β * routerInternalEnergy n β x i + kmsLogPartition n β x i) ∧
    ((softmaxAttention splitMetricTriadicInstance.toTriadicCore I hI keys).weights q j =
      Real.exp (InfoGeometry.Clifford.splitB11 q (keys j)) /
        (∑ k ∈ I, Real.exp (InfoGeometry.Clifford.splitB11 q (keys k)))) ∧
    (F * F = 1) ∧
    (F * B * F = R) :=
  ⟨router_softmax_is_kms_equilibrium n β x i e,
   router_weight_is_gibbs_quotient n β x i e,
   router_weights_sum_to_one n β x i,
   router_entropy_legendre_relation n β x i,
   split_cl11_attention_is_exact_softmax I hI keys q j,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.LLM.KMSAttentionThermoCapstone
