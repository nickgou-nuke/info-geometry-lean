import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

/-!
# A finite causal synthesis of recurring repository archetypes

This file records a small, kernel-checkable core shared by several otherwise
unrelated proposals: positive finite weights can be normalized and the
normalization is invariant under a common score shift.  The statements
deliberately stop at these finite algebraic facts; they do not assert an
analytic or physical limit.
-/

namespace InfoGeometry.Canonical.ArchetypeCausalSynthesis

open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def partition (w : ι → ℝ) : ℝ := ∑ i, w i

def normalized (w : ι → ℝ) (i : ι) : ℝ := w i / partition w

theorem partition_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    0 < partition w := by
  unfold partition
  exact Finset.sum_pos' (fun i _ => (hw i).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, hw _⟩

theorem normalized_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpart : 0 < partition w) (i : ι) :
    0 ≤ normalized w i := by
  unfold normalized
  exact div_nonneg (hw i) hpart.le

theorem normalized_sum_one (w : ι → ℝ) (hpart : 0 < partition w) :
    ∑ i, normalized w i = 1 := by
  unfold normalized partition
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpart)

theorem normalized_eq_of_common_scale (w : ι → ℝ) {c : ℝ}
    (hc : c ≠ 0) (i : ι) :
    normalized (fun j => c * w j) i = normalized w i := by
  unfold normalized partition
  simp only [Pi.mul_apply]
  have hsum : (∑ j, c * w j) = c * ∑ j, w j := by
    rw [Finset.mul_sum]
  rw [hsum]
  field_simp [hc]

theorem normalized_eq_of_common_shift_exp (s : ι → ℝ) (a : ℝ)
    (i : ι) :
    normalized (fun j => Real.exp (s j + a)) i =
      normalized (fun j => Real.exp (s j)) i := by
  simp_rw [Real.exp_add]
  convert normalized_eq_of_common_scale (fun j => Real.exp (s j))
      (Real.exp_ne_zero a) i using 1 <;>
    simp [mul_comm]

theorem normalized_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (i : ι) : 0 < normalized w i := by
  exact div_pos (hw i) (partition_pos w hw)

end
end InfoGeometry.Canonical.ArchetypeCausalSynthesis
