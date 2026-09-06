import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-!
# Word-Kernel Factorization of the Canonical Gauge State

This file establishes only the word-kernel level factorization of the canonical
gauge functional on monomial pairs $(u, v) \in \operatorname{List Bool} \times
\operatorname{List Bool}$.  The two kernels below are not yet a linear
conditional expectation or a positive trace on a norm-closed C*-algebra:

$$\boxed{\varphi_{\mathrm{word}}(u, v) = \begin{cases} \tau_{\mathrm{word}}(u, v) & \text{if } |u| = |v| \\ 0 & \text{if } |u| \neq |v| \end{cases}}$$

where:
1. $E_{\mathrm{word}} : \operatorname{List Bool} \times \operatorname{List Bool} \to \operatorname{Option}(\operatorname{List Bool} \times \operatorname{List Bool})$
   is the degree filter on word pairs:
   $$E_{\mathrm{word}}(u, v) = \begin{cases} \operatorname{some}(u, v) & \text{if } |u| = |v| \\ \operatorname{none} & \text{if } |u| \neq |v| \end{cases}$$
2. $\tau_{\mathrm{word}}(u, v) = \delta_{uv} 2^{-|u|}$ is the tracial kernel on equal-length words.

## Key Theorems Proved:
1. `gaugeConditionalExpectationWord`: Projects out cross-degree word pairs ($|u| \neq |v|$).
2. `uhfTracialStateWord`: Evaluates the finite matrix-unit trace kernel.
3. `canonicalGaugeState_word_factorization`: Exact word-level factorization through those two kernels.
4. `uhfTracialStateWord_matrixUnit_comm`: Tracial commutativity $\tau(E_{u,v} E_{x,y}) = \tau(E_{x,y} E_{u,v})$.
5. `gaugeConditionalExpectationWord_idempotent`: Idempotence of the word filter.
6. `uhfTracialState_partition_sum`: Full normalization $\sum_{|w|=n} \tau_{\mathrm{word}}(w, w) = 1$.
-/

noncomputable section

open Complex
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeUHFFactorizationBridge

/-- The gauge degree filter on a word pair.  This is an `Option`-valued
    word-level filter, not yet an algebra map $E : A \to A$. -/
def gaugeConditionalExpectationWord (u v : List Bool) : Option (List Bool × List Bool) :=
  if u.length = v.length then some (u, v) else none

/-- Finite matrix-unit trace kernel $\tau_{\mathrm{word}}$:
    it annihilates off-diagonal pairs and assigns weight $2^{-|u|}$ to
    diagonal words.  No completed UHF trace is defined here. -/
def uhfTracialStateWord (u v : List Bool) : ℂ :=
  if u = v then (1 / 2 : ℂ) ^ u.length else 0

/-- 🏆 THEOREM 1: Word-level factorization of the canonical gauge kernel. -/
theorem canonicalGaugeState_word_factorization (u v : List Bool) :
    canonicalGaugeState u v =
      match gaugeConditionalExpectationWord u v with
      | some (u', v') => uhfTracialStateWord u' v'
      | none => 0 := by
  dsimp [gaugeConditionalExpectationWord, uhfTracialStateWord]
  rw [canonicalGaugeState_word]
  by_cases huv : u = v
  · subst huv
    simp
  · by_cases hlen : u.length = v.length
    · simp [hlen, huv]
    · simp [hlen, huv]

/-- Compatibility alias for `canonicalGaugeState_word_factorization`. -/
abbrev canonicalGaugeState_eq_uhf_comp_gauge (u v : List Bool) :
    canonicalGaugeState u v =
      match gaugeConditionalExpectationWord u v with
      | some (u', v') => uhfTracialStateWord u' v'
      | none => 0 :=
  canonicalGaugeState_word_factorization u v

/-- 🏆 THEOREM 2: Tracial symmetry of the finite word kernel on matrix units.
    For matrix units $E_{u,v}$ and $E_{x,y}$ with $|u|=|v|$:
    $$\tau(E_{u,v} E_{x,y}) = \tau(E_{x,y} E_{u,v})$$ -/
theorem uhfTracialStateWord_matrixUnit_comm (u v x y : List Bool)
    (hu : u.length = v.length) :
    (if v = x then uhfTracialStateWord u y else 0) =
      (if y = u then uhfTracialStateWord x v else 0) := by
  dsimp [uhfTracialStateWord]
  by_cases h_vx : v = x
  · subst h_vx
    by_cases h_uy : u = y
    · subst h_uy
      simp only [if_true]
      rw [hu]
    · have h_yu : y ≠ u := ne_comm.mp h_uy
      simp [if_neg h_uy, if_neg h_yu]
  · have h_xv : x ≠ v := ne_comm.mp h_vx
    simp [if_neg h_vx, if_neg h_xv]

/-- Compatibility alias for `uhfTracialStateWord_matrixUnit_comm`. -/
theorem uhfTracialState_matrix_comm (u v x y : List Bool)
    (hu : u.length = v.length)
    (_hx : x.length = y.length)
    (_h_level : v.length = x.length) :
    (if v = x then uhfTracialStateWord u y else 0) =
      (if y = u then uhfTracialStateWord x v else 0) :=
  uhfTracialStateWord_matrixUnit_comm u v x y hu

/-- 🏆 THEOREM 3: Idempotence of the word filter. -/
theorem gaugeConditionalExpectationWord_idempotent (u v : List Bool) :
    (match gaugeConditionalExpectationWord u v with
     | some (u', v') => gaugeConditionalExpectationWord u' v'
     | none => none) = gaugeConditionalExpectationWord u v := by
  by_cases hlen : u.length = v.length <;>
    simp [gaugeConditionalExpectationWord, hlen]

/-- Compatibility alias for `gaugeConditionalExpectationWord_idempotent`. -/
abbrev gaugeConditionalExpectation_idempotent (u v : List Bool) :=
  gaugeConditionalExpectationWord_idempotent u v

/-- 🏆 THEOREM 4: Normalization of $\tau_{\mathrm{word}}$ on the full partition of unity at level $n$. -/
theorem uhfTracialState_partition_sum (n : ℕ) :
    ∑ w : BitWord n,
      uhfTracialStateWord (List.ofFn w) (List.ofFn w) = 1 := by
  classical
  simp [uhfTracialStateWord, List.length_ofFn, Finset.sum_const]

end InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeUHFFactorizationBridge
