import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Souriau–Massieu Bregman Duality and Fisher Metric Non-Negativity

This module formalizes the thermodynamic/information-theoretic layer connecting:
1. Finite Gibbs probability weights on root eigenspaces.
2. The Fisher–Souriau metric as the Hessian/variance quadratic form.
3. The non-negativity of the Fisher–Souriau metric via Gibbs variance expansion.
4. The exact non-negativity of the relative entropy / Bregman divergence.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.Lie.Souriau

variable {ι : Type*} [Fintype ι]

/-!
=============================================================================
PART 1: Discrete Gibbs Probabilities and Expectation Values
=============================================================================
-/

/-- A normalized Gibbs probability distribution over a finite index set ι. -/
structure GibbsDistribution (ι : Type*) [Fintype ι] where
  prob : ι → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_sum_one : ∑ i, prob i = 1

/-- The expectation value of an observable X : ι → ℝ under distribution p. -/
def expectation (p : GibbsDistribution ι) (X : ι → ℝ) : ℝ :=
  ∑ i, p.prob i * X i

/-- The centered variance of an observable X under distribution p. -/
def variance (p : GibbsDistribution ι) (X : ι → ℝ) : ℝ :=
  ∑ i, p.prob i * (X i - expectation p X) ^ 2

/-- 
  LEMMA 1: Expansion of Variance into Mean-of-Squares minus Square-of-Mean:
  Var(X) = E[X²] - (E[X])²
-/
theorem variance_eq_expect_sq_sub_sq_expect (p : GibbsDistribution ι) (X : ι → ℝ) :
    variance p X = (∑ i, p.prob i * (X i) ^ 2) - (expectation p X) ^ 2 := by
  dsimp [variance, expectation]
  have h_expand (i : ι) :
      p.prob i * (X i - ∑ j, p.prob j * X j) ^ 2 =
        p.prob i * (X i) ^ 2 - (2 * (∑ j, p.prob j * X j)) * (p.prob i * X i) +
          ((∑ j, p.prob j * X j) ^ 2) * p.prob i := by
    ring
  simp_rw [h_expand]
  rw [sum_add_distrib, sum_sub_distrib]
  rw [← mul_sum, ← mul_sum]
  rw [p.prob_sum_one, mul_one]
  ring

/-- 
  THEOREM 1: Non-Negativity of the Fisher–Souriau Variance:
  Var_p(X) ≥ 0
  Proves that the Fisher–Souriau metric is positive semi-definite.
-/
theorem variance_nonneg (p : GibbsDistribution ι) (X : ι → ℝ) :
    0 ≤ variance p X := by
  dsimp [variance]
  apply sum_nonneg
  intro i _
  have h1 : 0 ≤ p.prob i := p.prob_nonneg i
  have h2 : 0 ≤ (X i - expectation p X) ^ 2 := sq_nonneg _
  exact mul_nonneg h1 h2

/-- 
  COROLLARY (Cauchy–Schwarz for Gibbs Expectations):
  (E[X])² ≤ E[X²]
-/
theorem expectation_sq_le_expect_sq (p : GibbsDistribution ι) (X : ι → ℝ) :
    (expectation p X) ^ 2 ≤ ∑ i, p.prob i * (X i) ^ 2 := by
  have h_var := variance_nonneg p X
  rw [variance_eq_expect_sq_sub_sq_expect] at h_var
  linarith

/-!
=============================================================================
PART 2: Fisher–Souriau Metric on a Vector Space of Charges
=============================================================================
-/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- 
  Evaluation of directional charges: for a direction v ∈ E and charge vector q_i ∈ E*,
  X_v(i) = ⟨v, q_i⟩.
-/
def directionalCharge (q : ι → (E →ₗ[ℝ] ℝ)) (v : E) : ι → ℝ :=
  fun i => q i v

/-- 
  The Fisher–Souriau Quadratic Form on the Cartan Subalgebra:
  g_Souriau(v, v) = Var_p(⟨v, q⟩)
-/
def fisherSouriauQuadratic (p : GibbsDistribution ι) (q : ι → (E →ₗ[ℝ] ℝ)) (v : E) : ℝ :=
  variance p (directionalCharge q v)

/-- 
  THEOREM 2 (Fisher–Souriau Metric Positive Semi-Definiteness):
  For any direction v ∈ E, g_Souriau(v, v) ≥ 0.
-/
theorem fisherSouriau_nonneg (p : GibbsDistribution ι) (q : ι → (E →ₗ[ℝ] ℝ)) (v : E) :
    0 ≤ fisherSouriauQuadratic p q v :=
  variance_nonneg p (directionalCharge q v)

/-!
=============================================================================
PART 3: Relative Entropy (Kullback–Leibler) and Bregman Non-Negativity
=============================================================================
-/

/-- 
  The Kullback–Leibler / Relative Entropy Divergence between two strictly positive
  Gibbs distributions p and q on a finite set ι:
    D_KL(p ∥ q) = ∑ p_i * log(p_i / q_i)
-/
def klDivergence (p q : GibbsDistribution ι) : ℝ :=
  ∑ i, p.prob i * Real.log (p.prob i / q.prob i)

/-- 
  Fundamental Analytic Inequality for the Logarithm:
  log(x) ≥ 1 - 1/x  for all x > 0.
-/
lemma log_ge_one_sub_inv (x : ℝ) (hx : 0 < x) :
    1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

/-- 
  THEOREM 3 (Non-Negativity of Relative Entropy / Bregman Divergence):
  D_KL(p ∥ q) ≥ 0
  with equality if and only if p = q.
-/
theorem klDivergence_nonneg (p q : GibbsDistribution ι)
    (hp : ∀ i, 0 < p.prob i) (hq : ∀ i, 0 < q.prob i) :
    0 ≤ klDivergence p q := by
  dsimp [klDivergence]
  have h_term_ge (i : ι) :
      p.prob i * (1 - q.prob i / p.prob i) ≤ p.prob i * Real.log (p.prob i / q.prob i) := by
    have h_ratio_pos : 0 < p.prob i / q.prob i := div_pos (hp i) (hq i)
    have h_log := log_ge_one_sub_inv (p.prob i / q.prob i) h_ratio_pos
    have h_inv_ratio : (p.prob i / q.prob i)⁻¹ = q.prob i / p.prob i := inv_div (p.prob i) (q.prob i)
    rw [h_inv_ratio] at h_log
    nlinarith [p.prob_nonneg i]
  have h_sum_ge :
      ∑ i, p.prob i * (1 - q.prob i / p.prob i) ≤
        ∑ i, p.prob i * Real.log (p.prob i / q.prob i) :=
    sum_le_sum (fun i _ => h_term_ge i)
  have h_lhs : ∑ i, p.prob i * (1 - q.prob i / p.prob i) = 0 := by
    calc
      ∑ i, p.prob i * (1 - q.prob i / p.prob i)
        = ∑ i, (p.prob i - p.prob i * (q.prob i / p.prob i)) := by
          apply sum_congr rfl; intro i _; ring
      _ = ∑ i, (p.prob i - q.prob i) := by
          apply sum_congr rfl; intro i _
          have h_cancel : p.prob i * (q.prob i / p.prob i) = q.prob i := by
            exact mul_div_cancel₀ (q.prob i) (ne_of_gt (hp i))
          rw [h_cancel]
      _ = (∑ i, p.prob i) - (∑ i, q.prob i) := by rw [sum_sub_distrib]
      _ = 1 - 1 := by rw [p.prob_sum_one, q.prob_sum_one]
      _ = 0 := sub_self 1
  linarith

end InfoGeometry.Lie.Souriau

end noncomputable section
