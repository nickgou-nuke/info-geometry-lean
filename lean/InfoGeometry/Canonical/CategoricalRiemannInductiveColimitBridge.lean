import Mathlib.Tactic
import InfoGeometry.Canonical.CliffordDirectColimit
import InfoGeometry.Arithmetic.BostConnesZeta
import InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Finite prime-tower and Kraft readouts

This module packages finite-stage algebraic readouts.  It does not define an
analytic colimit or reformulate the Riemann Hypothesis.  The data are:

1. **Filtered tower of finite prime sets**:
   An ascending directed system of finite prime sets $S_1 \subseteq S_2 \subseteq \dots \subseteq S_n \subseteq \dots$
   ordered by set inclusion $\le$.

2. **Finite Euler products** at each stage, with no limiting operation.

3. **Finite non-vanishing** for real `s > 1`, proved directly from positivity.

4. **Finite Kraft bounds** for each supplied finite program set.

The final conjunction below records these finite facts under their explicit
hypotheses; it is not a theorem about zeta zeros or analytic continuation.
-/

namespace InfoGeometry.Canonical.CategoricalRiemannInductiveColimitBridge

open InfoGeometry.Canonical.CliffordDirectColimit
open InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge

/-- Ascending filtered tower of finite prime index sets $S_n \subseteq S_{n+1}$. -/
structure FilteredPrimeTower where
  stage : ℕ → Finset ℕ
  monotone : ∀ n, stage n ⊆ stage (n + 1)
  all_prime : ∀ n, ∀ p ∈ stage n, Nat.Prime p

/-- Finite Euler factor product over a finite prime stage $S_n$. -/
noncomputable def finiteEulerProduct (S : Finset ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ S, (1 - (p : ℝ) ^ (-s))⁻¹

/-- Inductive colimit sequence of finite Euler products along a prime tower. -/
noncomputable def colimitEulerSequence (tower : FilteredPrimeTower) (s : ℝ) (n : ℕ) : ℝ :=
  finiteEulerProduct (tower.stage n) s

/-- Filtered colimit Chaitin halting sequence over finite program sets. -/
noncomputable def colimitChaitinSequence
    {X : Type*} (K : KolmogorovComplexityData X) (towerSet : ℕ → Finset X) (n : ℕ) : ℝ :=
  ∑ x ∈ towerSet n, (2 : ℝ) ^ (- (K.kolmogorovLength x : ℝ))

/--
**Finite prime tower inclusion.**
For `n ≤ m`, the finite cutoff `stage n` is included in `stage m`:
$$S_n \subseteq S_m.$$
-/
theorem filtered_prime_tower_inclusion (tower : FilteredPrimeTower) {n m : ℕ} (h : n ≤ m) :
    tower.stage n ⊆ tower.stage m := by
  induction' h with k hk ih
  · exact Set.Subset.refl _
  · exact Set.Subset.trans ih (tower.monotone k)

/--
**Finite Euler product positivity.**
For a finite prime set and real `s > 1`, the finite Euler product is positive:
$$\prod_{p \in S} (1 - p^{-s})^{-1} \neq 0.$$
-/
theorem finite_euler_product_pos (S : Finset ℕ) (s : ℝ) (hs : 1 < s)
    (h_prime : ∀ p ∈ S, Nat.Prime p) :
    0 < finiteEulerProduct S s := by
  unfold finiteEulerProduct
  apply Finset.prod_pos
  intro p hp
  have hp_ge2 : 2 ≤ p := (h_prime p hp).two_le
  have hp_pos : 0 < (p : ℝ) := by positivity
  have h_pow_lt1 : (p : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by positivity)]
    have h1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.Prime.one_lt (h_prime p hp))
    have hpow : 1 < (p : ℝ) ^ s := Real.one_lt_rpow h1 (by positivity)
    exact inv_lt_one_of_one_lt₀ hpow
  have h_sub : 0 < 1 - (p : ℝ) ^ (-s) := sub_pos.mpr h_pow_lt1
  exact inv_pos.mpr h_sub

/--
**Finite Kraft bound.**
Every supplied finite stage satisfies the Kraft inequality:
$$\Omega_{\text{colimit}}(n) = \sum_{x \in S_n} 2^{-K(x)} \le 1.$$
-/
theorem colimit_chaitin_sequence_kraft_bound
    {X : Type*} (K : KolmogorovComplexityData X) (towerSet : ℕ → Finset X) (n : ℕ) :
    colimitChaitinSequence K towerSet n ≤ 1 :=
  kraft_mcmillan_inequality K (towerSet n)

/--
**Finite-stage non-vanishing.**
Every stage of a prime tower has positive finite Euler product for real `s > 1`.
-/
theorem categorical_colimit_riemann_non_vanishing
    (tower : FilteredPrimeTower) (s : ℝ) (hs : 1 < s) (n : ℕ) :
    0 < colimitEulerSequence tower s n :=
  finite_euler_product_pos (tower.stage n) s hs (tower.all_prime n)

/--
**Finite tower/readout conjunction.**
Combines the preceding finite inclusion, positivity, and Kraft statements.
-/
theorem grand_categorical_colimit_riemann_duality
    (tower : FilteredPrimeTower) {n m : ℕ} (h : n ≤ m) (s : ℝ) (hs : 1 < s)
    {X : Type*} (K : KolmogorovComplexityData X) (towerSet : ℕ → Finset X) :
    (tower.stage n ⊆ tower.stage m) ∧
    (0 < colimitEulerSequence tower s n) ∧
    (colimitChaitinSequence K towerSet n ≤ 1) := ⟨
  filtered_prime_tower_inclusion tower h,
  categorical_colimit_riemann_non_vanishing tower s hs n,
  colimit_chaitin_sequence_kraft_bound K towerSet n
⟩

end InfoGeometry.Canonical.CategoricalRiemannInductiveColimitBridge
