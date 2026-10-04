import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic

open MeasureTheory
open Set
open scoped ENNReal

namespace InfoGeometry.Probability

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {I : Type*} [Fintype I]

/--
The abstract core of the Additive Gluing Inequality.
Given a partition of the "reach relay" event `E` into disjoint "first relay" events `E_i`,
and "relay reaches destination" events `F_i`, if the failure probability 
`μ(E_i \ F_i) ≤ T * μ(E_i)` for all `i`, then the total success probability is 
at least `μ(E) - T`.
-/
theorem additive_gluing_inequality
    (E : I → Set Ω) (F : I → Set Ω)
    (h_meas_E : ∀ i, MeasurableSet (E i))
    (h_meas_F : ∀ i, MeasurableSet (F i))
    (h_disjoint : Pairwise (fun i j => Disjoint (E i) (E j)))
    (T : ℝ≥0∞)
    (h_cond : ∀ i, μ ((E i) \ (F i)) ≤ T * μ (E i)) :
    μ (⋃ i, E i) ≤ μ (⋃ i, (E i) ∩ (F i)) + T := by
  have h1 : μ (⋃ i, E i) = ∑' i, μ (E i) := measure_iUnion h_disjoint h_meas_E
  have h_disjoint2 : Pairwise (fun i j => Disjoint (E i ∩ F i) (E j ∩ F j)) := by
    intro i j hij
    exact Disjoint.mono inter_subset_left inter_subset_left (h_disjoint hij)
  have h2 : μ (⋃ i, E i ∩ F i) = ∑' i, μ (E i ∩ F i) := by
    apply measure_iUnion h_disjoint2
    intro i
    exact (h_meas_E i).inter (h_meas_F i)
  
  have heq : ∀ i, μ (E i) = μ (E i ∩ F i) + μ (E i \ F i) := by
    intro i
    have h_diff : E i = (E i ∩ F i) ∪ (E i \ F i) := by
      ext x
      simp only [mem_union, mem_inter_iff, mem_diff]
      tauto
    nth_rw 1 [h_diff]
    apply measure_union
    · exact disjoint_left.mpr (by intro x hx1 hx2; exact hx2.2 hx1.2)
    · exact (h_meas_E i).diff (h_meas_F i)
  
  rw [h1, h2]
  have hsum : ∑' i, μ (E i) = (∑' i, μ (E i ∩ F i)) + ∑' i, μ (E i \ F i) := by
    simp_rw [heq]
    exact ENNReal.tsum_add
    
  rw [hsum]
  
  have h_bound : ∑' i, μ (E i \ F i) ≤ ∑' i, T * μ (E i) := by
    apply ENNReal.tsum_le_tsum h_cond
    
  have h_pull : ∑' i, T * μ (E i) = T * ∑' i, μ (E i) := by
    exact ENNReal.tsum_mul_left
    
  have h_prob : ∑' i, μ (E i) ≤ 1 := by
    rw [← h1]
    calc
      μ (⋃ i, E i) ≤ μ Set.univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      
  have h_final : ∑' i, μ (E i \ F i) ≤ T := by
    calc
      ∑' i, μ (E i \ F i) ≤ ∑' i, T * μ (E i) := h_bound
      _ = T * ∑' i, μ (E i) := h_pull
      _ ≤ T * 1 := by gcongr
      _ = T := mul_one T
      
  exact add_le_add (le_refl _) h_final

end InfoGeometry.Probability
