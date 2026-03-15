import InfoGeometry.Basic
import InfoGeometry.MaxEnt.Finite
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace InfoGeometry.Sandbox

open Real Set InfoGeometry

variable {Y T : Type*} [Fintype Y] [Fintype T]
variable [DecidableEq Y] [DecidableEq T]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- 
Jensen's inequality for the logarithm (concavity form).
Derives from Mathlib's `strictConcaveOn_log_Ioi`.
-/
theorem log_jensen_sum
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (x : ι → ℝ) (hx_pos : ∀ i, 0 < x i) :
    ∑ i, w i * log (x i) ≤ log (∑ i, w i * x i) := by
  have h_conc := strictConcaveOn_log_Ioi.concaveOn
  have h_mem : ∀ i ∈ Finset.univ, x i ∈ Ioi 0 := fun i _ => hx_pos i
  exact h_conc.le_map_sum (fun i _ => hw_nonneg i) hw_sum h_mem

/--
Jensen's inequality for finite KL divergence: the KL divergence to a convex
combination of measures is bounded by the convex combination of KL divergences.
-/
lemma fin_kl_div_convex_le
    (p : FinProb Y)
    (w : T → ℝ) (hw_nonneg : ∀ t, 0 ≤ w t) (hw_sum : ∑ t, w t = 1)
    (q : T → FinProb Y)
    (hpos_p : ∀ y, 0 < (p y).toReal)
    (hpos_q : ∀ t y, 0 < (q t y).toReal) :
    let q_mix : Y → ℝ := fun y => ∑ t, w t * (q t y).toReal
    (∑ y, (p y).toReal * Real.log ((p y).toReal / q_mix y))
      ≤ ∑ t, w t * (∑ y, (p y).toReal * Real.log ((p y).toReal / (q t y).toReal)) := by
  intro q_mix
  have h_slice : ∀ y, ∑ t, w t * log (q t y).toReal ≤ log (q_mix y) := by
    intro y
    unfold q_mix
    apply log_jensen_sum w hw_nonneg hw_sum
    intro t
    exact hpos_q t y

  have h_sum : ∑ y, (p y).toReal * (∑ t, w t * log (q t y).toReal) ≤ ∑ y, (p y).toReal * log (q_mix y) := by
    apply Finset.sum_le_sum
    intro y _hy
    apply mul_le_mul_of_nonneg_left (h_slice y) (p y).toReal_nonneg

  have h_comm : ∑ y, (p y).toReal * (∑ t, w t * log (q t y).toReal) = ∑ t, w t * (∑ y, (p y).toReal * log (q t y).toReal) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_comm (p _).toReal, mul_assoc, ← Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t _ht
    rw [mul_comm]

  have h_split_lhs : (∑ y, (p y).toReal * Real.log ((p y).toReal / q_mix y)) = 
      (∑ y, (p y).toReal * Real.log (p y).toReal) - (∑ y, (p y).toReal * Real.log (q_mix y)) := by
    simp_rw [log_div (hpos_p _).ne' (show q_mix _ ≠ 0 from by
      apply (Finset.sum_pos _ _).ne'
      · intro t _ht; exact mul_nonneg (hw_nonneg t) (hpos_q t _ |>.le)
      · have : ∃ t, 0 < w t := by
          by_contra! h; have : ∑ t, w t ≤ 0 := Finset.sum_nonpos (fun t _ => h t); linarith
        rcases this with ⟨t0, ht0⟩; exact ⟨t0, Finset.mem_univ t0, mul_pos ht0 (hpos_q t0 _)⟩),
      mul_sub, Finset.sum_sub_distrib]

  have h_split_rhs : (∑ t, w t * (∑ y, (p y).toReal * Real.log ((p y).toReal / (q t y).toReal))) = 
      (∑ y, (p y).toReal * Real.log (p y).toReal) - (∑ t, w t * ∑ y, (p y).toReal * Real.log (q t y).toReal) := by
    simp_rw [log_div (hpos_p _).ne' (hpos_q _ _).ne', mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, hw_sum, one_mul]

  rw [h_split_lhs, h_split_rhs, ← h_comm]
  exact sub_le_sub_left h_sum _

end InfoGeometry.Sandbox
