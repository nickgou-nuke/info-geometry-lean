import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Discrete Vector-Spin Markov Kernel for Attention Architectures

This module formalizes the discrete stochastic Markov kernel for vector spins
in mean-field transformer models:
1. Finite configuration space: configurations $S : \mathcal{V} \to \Sigma$ on finite token nodes $\mathcal{V}$
   over a finite spin alphabet $\Sigma$.
2. Single-site effective field and Hamiltonian $H_i(s; S, X)$.
3. Single-site Boltzmann factor $\exp(-\beta H_i(s; S, X))$ and local partition function $Z_i(S, X)$.
4. Single-site Gibbs kernel $P_i(s \mid S, X)$ on the simplex $\Delta^{|\Sigma|-1}$.
5. Synchronous product Markov transition kernel:
     $$P(S' \mid S, X) = \prod_{i \in \mathcal{V}} P_i(S'_i \mid S, X).$$
6. Core Theorems:
   - `localPartition_pos`: $Z_i(S, X) > 0$.
   - `singleSiteGibbs_pos`: $P_i(s \mid S, X) > 0$.
   - `singleSiteGibbs_sum_one`: $\sum_{s \in \Sigma} P_i(s \mid S, X) = 1$.
   - `productKernel_pos`: $P(S' \mid S, X) > 0$.
   - `productKernel_sum_one`: $\sum_{S' \in (\mathcal{V} \to \Sigma)} P(S' \mid S, X) = 1$.

All proofs are complete with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.LLM

variable {Sigma : Type*} [Fintype Sigma]

/-- Single-site local partition function (normalizer) at temperature inverse $\beta > 0$. -/
def localPartition {V : Type*} (beta : ℝ) (H : V → Sigma → ℝ) (i : V) : ℝ :=
  ∑ s : Sigma, Real.exp (-beta * H i s)

/-- The local partition function is strictly positive when $\Sigma$ is nonempty. -/
theorem localPartition_pos {V : Type*} [Nonempty Sigma] (beta : ℝ) (H : V → Sigma → ℝ) (i : V) :
    0 < localPartition beta H i := by
  dsimp [localPartition]
  apply Finset.sum_pos'
  · intro s _
    exact le_of_lt (Real.exp_pos (-beta * H i s))
  · obtain ⟨s0⟩ := (inferInstance : Nonempty Sigma)
    exact ⟨s0, Finset.mem_univ s0, Real.exp_pos (-beta * H i s0)⟩

/-- Single-site Gibbs probability distribution $P_i(s \mid H)$. -/
def singleSiteGibbs {V : Type*} (beta : ℝ) (H : V → Sigma → ℝ) (i : V) (s : Sigma) : ℝ :=
  Real.exp (-beta * H i s) / localPartition beta H i

/-- The single-site Gibbs probability is strictly positive. -/
theorem singleSiteGibbs_pos {V : Type*} [Nonempty Sigma] (beta : ℝ) (H : V → Sigma → ℝ) (i : V) (s : Sigma) :
    0 < singleSiteGibbs beta H i s := by
  dsimp [singleSiteGibbs]
  exact div_pos (Real.exp_pos (-beta * H i s)) (localPartition_pos beta H i)

/-- The single-site Gibbs distribution sums to 1 on $\Sigma$. -/
theorem singleSiteGibbs_sum_one {V : Type*} [Nonempty Sigma] (beta : ℝ) (H : V → Sigma → ℝ) (i : V) :
    ∑ s : Sigma, singleSiteGibbs beta H i s = 1 := by
  dsimp [singleSiteGibbs]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (localPartition_pos beta H i))

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Synchronous product Markov transition kernel $P(S' \mid S, H) = \prod_{i \in V} P_i(S'_i \mid H)$. -/
def productKernel (beta : ℝ) (H : V → Sigma → ℝ) (S_next : V → Sigma) : ℝ :=
  ∏ i : V, singleSiteGibbs beta H i (S_next i)

/-- The product Markov kernel is strictly positive on every configuration $S'$. -/
theorem productKernel_pos [Nonempty Sigma] (beta : ℝ) (H : V → Sigma → ℝ) (S_next : V → Sigma) :
    0 < productKernel beta H S_next := by
  dsimp [productKernel]
  apply Finset.prod_pos
  intro i _
  exact singleSiteGibbs_pos beta H i (S_next i)

/-- The synchronous product Markov kernel sums to 1 over all configurations $S' \in (V \to \Sigma)$. -/
theorem productKernel_sum_one [Nonempty Sigma] (beta : ℝ) (H : V → Sigma → ℝ) :
    ∑ S_next : V → Sigma, productKernel beta H S_next = 1 := by
  dsimp [productKernel]
  rw [← Fintype.prod_sum]
  have h : ∀ i : V, (∑ s : Sigma, singleSiteGibbs beta H i s) = 1 := by
    intro i
    exact singleSiteGibbs_sum_one beta H i
  simp_rw [h]
  exact Finset.prod_const_one

end InfoGeometry.LLM
