import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Log-sum inequality and analytic primitives

Log-sum inequality and corollaries for DPI.
-/

open scoped BigOperators

namespace InfoGeometry.Projective

/-- Log-sum inequality (finite form), used as the core inequality in DPI proofs. -/
theorem logSum_inequality
    {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ)
    (ha : ∀ i, i ∈ s → 0 < a i)
    (hb : ∀ i, i ∈ s → 0 < b i) :
    (∑ i ∈ s, a i * Real.log (a i / b i))
      ≥
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) := by
  -- Proof via Jensen's inequality for concave log
  have hbsum : 0 < ∑ i ∈ s, b i := by
    apply Finset.sum_pos
    intros i hi
    exact hb i hi
  have hasum : 0 < ∑ i ∈ s, a i := by
    apply Finset.sum_pos
    intros i hi
    exact ha i hi
  let p i := a i / (∑ i ∈ s, a i)
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    apply div_nonneg (le_of_lt (ha i (by simp))) (le_of_lt hasum)
  have hp_sum : ∑ i ∈ s, p i = 1 := by
    simp [p, Finset.sum_div, hasum.ne']
  calc
    (∑ i ∈ s, a i * Real.log (a i / b i))
      = (∑ i ∈ s, (∑ i ∈ s, a i) * p i * Real.log ((∑ i ∈ s, a i) * p i / b i)) := by
        simp [p, mul_assoc, mul_div_cancel' _ hasum.ne']
    _ = (∑ i ∈ s, (∑ i ∈ s, a i) * p i * (Real.log (p i) + Real.log ((∑ i ∈ s, a i) / b i))) := by
        congr; funext i
        rw [Real.log_mul (by positivity) (by positivity)]
    _ = (∑ i ∈ s, (∑ i ∈ s, a i) * p i * Real.log (p i)) +
        (∑ i ∈ s, (∑ i ∈ s, a i) * p i * Real.log ((∑ i ∈ s, a i) / b i)) := by
        rw [Finset.sum_add_distrib]
        congr; funext i
        ring
    _ = (∑ i ∈ s, a i * Real.log (p i)) +
        (∑ i ∈ s, a i * Real.log ((∑ i ∈ s, a i) / b i)) := by
        simp [p, mul_assoc]
    _ = (∑ i ∈ s, a i * Real.log (p i)) +
        (∑ i ∈ s, a i) * Real.log (∑ i ∈ s, a i) - (∑ i ∈ s, a i * Real.log (b i)) := by
        rw [Finset.sum_mul, ←Finset.sum_sub_distrib]
        congr; funext i
        rw [Real.log_div (by positivity) (by positivity)]
        ring
    _ ≥ (∑ i ∈ s, a i) * (∑ i ∈ s, p i * Real.log (p i)) +
        (∑ i ∈ s, a i) * Real.log (∑ i ∈ s, a i) - (∑ i ∈ s, a i * Real.log (b i)) := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_right
        apply Real.log_le_log_of_le (ha i hi) (le_of_lt hasum)
        apply hp_nonneg
        apply le_of_lt hasum
    _ = (∑ i ∈ s, a i) * (∑ i ∈ s, p i * Real.log (p i)) +
        (∑ i ∈ s, a i) * Real.log (∑ i ∈ s, a i) - (∑ i ∈ s, a i * Real.log (b i)) := rfl
    _ ≥ (∑ i ∈ s, a i) * Real.log (∑ i ∈ s, a i) - (∑ i ∈ s, a i * Real.log (b i)) := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left
        apply Real.sum_mul_log_le_log_sum hp_nonneg hp_sum
        apply le_of_lt hasum
    _ = (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) := by
        rw [←Real.log_div (by positivity) (by positivity)]
        ring

end InfoGeometry.Projective
