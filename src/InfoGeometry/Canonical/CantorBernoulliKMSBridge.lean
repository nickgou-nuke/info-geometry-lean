import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic

/-!
# Finite Bernoulli Weights and Tree Partition Function

This module establishes finite Bernoulli weight identities over the binary
Cantor tree:

1. **Critical Inverse Temperature:**
   $$\beta_c = \ln 2 \implies e^{-\beta_c} = \frac{1}{2}$$

2. **Critical-beta scalar scaling:**
   Multiplication by a supplied scalar is rescaled by the exact weight
   $e^{-\beta_c}=1/2$.

3. **Level-$n$ Partition Function Normalization:**
   $$\sum_{w \in \text{Fin}(2^n)} 2^{-n} = 1$$

4. **Martingale / Branching Additivity:**
   $$\mu(w0) + \mu(w1) = 2^{-(n+1)} + 2^{-(n+1)} = 2^{-n} = \mu(w)$$

The file does not define a KMS predicate, a Cuntz algebra action, or a
completed thermodynamic state; those require separate owners and hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliKMSBridge

open BigOperators Finset

/-- The distinguished finite Bernoulli scale `log 2`. -/
def criticalBeta : ℝ := Real.log 2

/-- 🏆 THEOREM 1: Exponential of Negative Critical Beta is Exactly One-Half -/
theorem exp_neg_criticalBeta :
    Real.exp (-criticalBeta) = 1 / 2 := by
  dsimp [criticalBeta]
  rw [Real.exp_neg]
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by positivity)
  rw [h2]
  ring

/-- 🏆 THEOREM 2: Critical-beta scalar weight identity. -/
theorem criticalBeta_weight_scaling (unit_weight : ℝ) :
    Real.exp (-criticalBeta) * unit_weight = (1 / 2 : ℝ) * unit_weight := by
  rw [exp_neg_criticalBeta]

/-- Inner product expectation functional for a normalized state vector in a Hilbert space -/
def hilbertStateExpectation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ω : E) (A : E →L[ℂ] E) : ℂ :=
  @inner ℂ E _ Ω (A Ω)

/-- 🏆 THEOREM 3: Normalization of the Identity Operator under Hilbert Vacuum -/
theorem hilbertStateExpectation_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ω : E) (hΩ : ‖Ω‖ = 1) :
    hilbertStateExpectation Ω (ContinuousLinearMap.id ℂ E) = 1 := by
  dsimp [hilbertStateExpectation]
  have h_norm_sq : @inner ℂ E _ Ω Ω = (‖Ω‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K Ω
  rw [h_norm_sq, hΩ]
  simp only [Complex.ofReal_one, one_pow]

/-- 🏆 THEOREM 4: Level-n Binary Partition Function Normalization -/
theorem binary_tree_partition_sum (n : ℕ) :
    (∑ _w : Fin (2^n), (1 / 2 : ℝ) ^ n) = 1 := by
  have h_card : (Finset.univ : Finset (Fin (2^n))).card = 2^n := Finset.card_fin (2^n)
  rw [Finset.sum_const, h_card, nsmul_eq_mul]
  have _h_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  calc
    ((2^n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by
      push_cast
      rfl
    _ = (2 * (1 / 2 : ℝ)) ^ n := by rw [mul_pow]
    _ = (1 : ℝ) ^ n := by
      congr 1
      ring
    _ = 1 := one_pow n

/-- 🏆 THEOREM 5: Branching Martingale Additivity of Cylinder Weights -/
theorem cylinder_weight_branching_sum (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n := by
  simp only [pow_succ]
  ring

/-- 🏆 THEOREM 6: Strict Positivity of Cylinder Weights at Arbitrary Depth -/
theorem cylinder_weight_pos (n : ℕ) :
    (0 : ℝ) < (1 / 2 : ℝ) ^ n := by
  positivity

end InfoGeometry.Canonical.CantorBernoulliKMSBridge
