import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace InfoGeometry.Epistemology.CrystallizedGrammar

open Set

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]

theorem maximizing_endpoints {domain : Set Space} {objective : Space → ℝ}
    (convex : ConvexOn ℝ domain objective) (maximum : ℝ)
    (bounded : ∀ point ∈ domain, objective point ≤ maximum)
    {first second optimum : Space} (first_mem : first ∈ domain) (second_mem : second ∈ domain)
    (between : optimum ∈ openSegment ℝ first second) (attained : objective optimum = maximum) :
    objective first = maximum ∧ objective second = maximum := by
  have first_bound : objective first ≤ objective optimum := by
    rw [attained]
    exact bounded first first_mem
  have second_bound : objective second ≤ objective optimum := by
    rw [attained]
    exact bounded second second_mem
  exact ⟨(first_bound.antisymm
    (convex.le_left_of_right_le first_mem second_mem between second_bound)).trans attained,
    (second_bound.antisymm
    (convex.le_right_of_left_le first_mem second_mem between first_bound)).trans attained⟩

theorem maximizer_set_isExtreme {domain : Set Space} {objective : Space → ℝ}
    (convex : ConvexOn ℝ domain objective) (maximum : ℝ)
    (bounded : ∀ point ∈ domain, objective point ≤ maximum) :
    IsExtreme ℝ domain {point ∈ domain | objective point = maximum} := by
  refine ⟨fun _ member => member.1, ?_⟩
  intro first first_mem second second_mem optimum optimum_mem between
  exact ⟨first_mem,
    (maximizing_endpoints convex maximum bounded first_mem second_mem between optimum_mem.2).1⟩

theorem linear_maximum_on_openSegment_iff (domain : Set Space)
    (objective : Space →ₗ[ℝ] ℝ) (maximum : ℝ)
    (bounded : ∀ point ∈ domain, objective point ≤ maximum)
    {first second optimum : Space} (first_mem : first ∈ domain) (second_mem : second ∈ domain)
    (between : optimum ∈ openSegment ℝ first second) :
    objective optimum = maximum ↔ objective first = maximum ∧ objective second = maximum := by
  constructor
  · intro attained
    have endpoints : ConvexOn ℝ (segment ℝ first second) objective :=
      objective.convexOn (convex_segment first second)
    have left_mem := left_mem_segment ℝ first second
    have right_mem := right_mem_segment ℝ first second
    exact maximizing_endpoints endpoints maximum
      (fun _ member => (endpoints.le_on_segment left_mem right_mem member).trans
        (max_le (bounded first first_mem) (bounded second second_mem)))
      left_mem right_mem between attained
  · rintro ⟨first_value, second_value⟩
    obtain ⟨firstWeight, secondWeight, _, _, weight_sum, combination⟩ := between
    rw [← combination, map_add, map_smul, map_smul, first_value, second_value]
    simp only [smul_eq_mul]
    rw [← add_mul, weight_sum, one_mul]

theorem unique_maximizer_extreme {domain : Set Space} {objective : Space → ℝ}
    (convex : ConvexOn ℝ domain objective) (optimum : Space)
    (member : optimum ∈ domain)
    (maximal : ∀ point ∈ domain, objective point ≤ objective optimum)
    (unique : ∀ point ∈ domain, objective point = objective optimum → point = optimum) :
    optimum ∈ domain.extremePoints ℝ := by
  refine ⟨member, ?_⟩
  intro first first_mem second second_mem between
  exact unique first first_mem
    (maximizing_endpoints convex (objective optimum) maximal first_mem second_mem between rfl).1

theorem unique_maximizer_mem_generators (generators : Set Space) (objective : Space → ℝ)
    (convex : ConvexOn ℝ (convexHull ℝ generators) objective) (optimum : Space)
    (member : optimum ∈ convexHull ℝ generators)
    (maximal : ∀ point ∈ convexHull ℝ generators, objective point ≤ objective optimum)
    (unique : ∀ point ∈ convexHull ℝ generators,
      objective point = objective optimum → point = optimum) : optimum ∈ generators :=
  extremePoints_convexHull_subset (unique_maximizer_extreme convex optimum member maximal unique)

theorem epistemic_crystallization (generators : Set Space) (objective : Space →ₗ[ℝ] ℝ)
    (maximum : ℝ)
    (bounded : ∀ point ∈ convexHull ℝ generators, objective point ≤ maximum)
    (optimum : Space) (member : optimum ∈ convexHull ℝ generators)
    (attained : objective optimum = maximum)
    (unique : ∀ point ∈ convexHull ℝ generators, objective point = maximum → point = optimum) :
    optimum ∈ generators := by
  refine unique_maximizer_mem_generators generators objective ?_ optimum member ?_ ?_
  · exact objective.convexOn (convex_convexHull ℝ generators)
  · intro point point_mem
    rw [attained]
    exact bounded point point_mem
  · intro point point_mem value
    exact unique point point_mem (value.trans attained)

theorem bound_on_convexHull (generators : Set Space) (objective : Space → ℝ)
    (convex : ConvexOn ℝ (convexHull ℝ generators) objective) (maximum : ℝ)
    (bounded : ∀ point ∈ generators, objective point ≤ maximum) :
    ∀ point ∈ convexHull ℝ generators, objective point ≤ maximum := by
  have inclusion : generators ⊆ {point ∈ convexHull ℝ generators | objective point ≤ maximum} := by
    intro point point_mem
    exact ⟨subset_convexHull ℝ generators point_mem, bounded point point_mem⟩
  have hull_inclusion := convexHull_min inclusion (convex.convex_le maximum)
  intro point point_mem
  exact (hull_inclusion point_mem).2

theorem finite_generator_maximum (generators : Finset Space) (nonempty : generators.Nonempty)
    (objective : Space → ℝ) (convex : ConvexOn ℝ (convexHull ℝ (↑generators : Set Space)) objective) :
    ∃ optimum ∈ generators,
      ∀ point ∈ convexHull ℝ (↑generators : Set Space), objective point ≤ objective optimum := by
  obtain ⟨optimum, member, maximal⟩ := generators.exists_max_image objective nonempty
  exact ⟨optimum, member, bound_on_convexHull generators objective convex (objective optimum) maximal⟩

end InfoGeometry.Epistemology.CrystallizedGrammar
