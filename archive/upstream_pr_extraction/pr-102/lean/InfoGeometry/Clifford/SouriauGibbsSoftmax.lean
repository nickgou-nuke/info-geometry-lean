import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic
import InfoGeometry.Analytic.LogSumExp
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace InfoGeometry.Clifford.SouriauThermodynamics

variable {I : Type*} [Fintype I]

/-!
# Finite Gibbs Softmax & Translation Invariance

This module formalizes finite normalized exponential weights and their
translation-index invariance:

$$\boxed{
\begin{aligned}
&\textbf{1. Partition Function Positivity: } Z(s) = \sum_{i} \exp(\beta s_i) > 0\\
&\textbf{2. Softmax Probability Normalization: } \sum_i \operatorname{softmax}_i(s) = 1\\
&\textbf{3. Shift Equivariance: } \operatorname{softmax}(s \circ \sigma) = \operatorname{softmax}(s) \circ \sigma\\
&\textbf{4. RoPE Topological Invariance: } s_{m+c}(n+c) = s_m(n) \implies p_{m+c}(n+c) = p_m(n).
\end{aligned}}
$$

The results are finite algebraic readout theorems.  This module does not
assert a coadjoint-orbit construction, a maximum-entropy variational theorem,
or a Clifford representation.
-/

/-! ### 1. Thermal State & Partition Function -/

/-- The Souriau Thermal State with strictly positive inverse temperature β.
    In Transformers, $\beta = 1 / \sqrt{d_{\mathrm{head}}}$. -/
structure ThermalState where
  beta : ℝ
  beta_pos : 0 < beta

/-- Partition Function (Z) computes the statistical sum over the context window. -/
noncomputable def partitionFunction (state : ThermalState) (energy : I → ℝ) : ℝ :=
  ∑ i : I, Real.exp (state.beta * energy i)

/-- Positivity of the partition function (since $\exp(x) > 0$ for all $x$). -/
theorem partitionFunction_pos [Nonempty I] (state : ThermalState) (energy : I → ℝ) :
    0 < partitionFunction state energy := by
  dsimp [partitionFunction]
  apply Finset.sum_pos
  · intro i _
    exact Real.exp_pos (state.beta * energy i)
  · exact Finset.univ_nonempty

/-- Non-zero partition function, strictly required for safe Softmax division. -/
theorem partitionFunction_ne_zero [Nonempty I] (state : ThermalState) (energy : I → ℝ) :
    partitionFunction state energy ≠ 0 :=
  ne_of_gt (partitionFunction_pos state energy)

/-! ### 2. The Souriau-Gibbs Softmax Operator -/

/--
  Finite Gibbs-style normalized exponential weight for state `j`.
-/
noncomputable def softmaxGibbs (state : ThermalState) (energy : I → ℝ) (j : I) : ℝ :=
  Real.exp (state.beta * energy j) / partitionFunction state energy

/--
  **THEOREM 1 (Conservation of Probability)**:
  Strictly proves that the Softmax distribution sums to exactly 1 over the context window:
  $$\sum_{i \in I} \operatorname{softmax}_i(E) = 1.$$
-/
theorem softmaxGibbs_sum_eq_one [Nonempty I] (state : ThermalState) (energy : I → ℝ) :
    ∑ i : I, softmaxGibbs state energy i = 1 := by
  dsimp [softmaxGibbs]
  rw [← Finset.sum_div]
  exact div_self (partitionFunction_ne_zero state energy)

/-! ### 3. Analytic frontier: derivative of the finite log-partition function -/

/--
The derivative of the finite log-partition function is the Gibbs-weighted
first moment.  This is a specialization of the analytic `logSumExp` owner;
it does not assert a variational, Wasserstein, or Ricci-flow interpretation.
-/
theorem partition_log_deriv_eq_weighted_mean [Nonempty I]
    (energy : I → ℝ) (beta : ℝ) :
    deriv (fun b : ℝ => Real.log (∑ i : I, Real.exp (b * energy i))) beta =
      (∑ i : I, energy i * Real.exp (beta * energy i)) /
        (∑ i : I, Real.exp (beta * energy i)) := by
  have heq : (fun b : ℝ => Real.log (∑ i : I, Real.exp (b * energy i))) =
      InfoGeometry.Analytic.logSumExp (fun _ : I => (1 : ℝ)) energy := by
    ext b
    simp [InfoGeometry.Analytic.logSumExp, InfoGeometry.Analytic.logSumExpPartition]
  rw [heq]
  have h := InfoGeometry.Analytic.logSumExp_deriv_eq_ratio
    (w := fun _ : I => (1 : ℝ)) (a := energy)
    (hw := fun _ => by norm_num) beta
  rw [h]
  simp only [InfoGeometry.Analytic.logSumExpMoment1,
    InfoGeometry.Analytic.logSumExpPartition, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/--
The log-partition derivative is the finite Gibbs-weighted energy mean at the
state's inverse temperature.  This is only a finite readout identity; it
does not assert a Wasserstein or Ricci-flow interpretation.
-/
theorem partition_log_deriv_eq_softmax_mean [Nonempty I]
    (state : ThermalState) (energy : I → ℝ) :
    deriv (fun b : ℝ => Real.log (∑ i : I, Real.exp (b * energy i))) state.beta =
      ∑ i : I, energy i * softmaxGibbs state energy i := by
  rw [partition_log_deriv_eq_weighted_mean energy state.beta]
  unfold softmaxGibbs partitionFunction
  simp only [div_eq_mul_inv]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]

/-! ### 4. Gauge Shift Invariance & Equivariance -/

/--
  **THEOREM 2 (Shift Invariance of the Partition Function)**:
  Any sequence permutation (such as a cyclic translation) leaves the thermodynamic
  partition function invariant:
  $$Z(E \circ \sigma) = Z(E).$$
-/
theorem partitionFunction_shift_invariant (state : ThermalState) (energy : I → ℝ) (sigma : I ≃ I) :
    partitionFunction state (energy ∘ sigma) = partitionFunction state energy := by
  dsimp [partitionFunction]
  exact Equiv.sum_comp sigma (fun x => Real.exp (state.beta * energy x))

/--
  **THEOREM 3 (Softmax Equivariance under Shift)**:
  The probability distribution correctly tracks the bijective transformation:
  $$\operatorname{softmax}_j(E \circ \sigma) = \operatorname{softmax}_{\sigma(j)}(E).$$
-/
theorem softmaxGibbs_shift_equivariance (state : ThermalState) (energy : I → ℝ) (sigma : I ≃ I) (j : I) :
    softmaxGibbs state (energy ∘ sigma) j = softmaxGibbs state energy (sigma j) := by
  dsimp [softmaxGibbs]
  rw [partitionFunction_shift_invariant state energy sigma]

/-! ### 5. RoPE Topological Coupling -/

variable {T : Type*} [AddCommGroup T] [Fintype T]

/-- Translation equivalence on an abelian index group: $x \mapsto x + c$. -/
def shiftEquiv (c : T) : T ≃ T :=
  Equiv.addRight c

/--
  **MASTER THEOREM (Thermodynamic RoPE Invariance Law)**:
  If the Attention energy strictly evaluates the relative distance f(n - m),
  shifting the absolute positions of both Query (m) and Key (n) by constant (c)
  yields exactly identical Gibbs probabilities:
  $$p_{m+c}(n+c) = p_m(n).$$
-/
theorem rope_softmax_invariance [Nonempty T]
    (state : ThermalState)
    (f : T → ℝ)
    (m n c : T) :
    softmaxGibbs (I := T) state (fun x => f (x - (m + c))) (n + c) =
    softmaxGibbs (I := T) state (fun x => f (x - m)) n := by
  have h_equiv : (fun x => f (x - (m + c))) =
      (fun y => f (y - m)) ∘ (shiftEquiv (-c)) := by
    ext y
    dsimp [shiftEquiv]
    congr 1
    abel
  rw [h_equiv]
  simpa [shiftEquiv] using
    (softmaxGibbs_shift_equivariance state (fun y => f (y - m))
      (shiftEquiv (-c)) (n + c))

/-! ### 6. Grand Thermodynamic Synthesis -/

/--
**Finite Gibbs/softmax synthesis**

Collects:
1. Positivity of statistical sum Z > 0.
2. Conservation of probability ∑ p_i = 1.
3. Partition function shift invariance Z(E ∘ σ) = Z(E).
4. Exact relative-position RoPE invariance p_{m+c}(n+c) = p_m(n).
-/
theorem grand_souriau_softmax_synthesis [Nonempty I] [Nonempty T]
    (state : ThermalState) (energy : I → ℝ) (sigma : I ≃ I)
    (f : T → ℝ) (m n c : T) :
    (0 < partitionFunction state energy ∧
     ∑ i : I, softmaxGibbs state energy i = 1 ∧
     partitionFunction state (energy ∘ sigma) = partitionFunction state energy) ∧
    (softmaxGibbs (I := T) state (fun x => f (x - (m + c))) (n + c) =
     softmaxGibbs (I := T) state (fun x => f (x - m)) n) :=
  ⟨⟨partitionFunction_pos state energy,
     softmaxGibbs_sum_eq_one state energy,
     partitionFunction_shift_invariant state energy sigma⟩,
   rope_softmax_invariance state f m n c⟩

end InfoGeometry.Clifford.SouriauThermodynamics
