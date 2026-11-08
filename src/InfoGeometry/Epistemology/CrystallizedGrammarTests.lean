import InfoGeometry.Epistemology.CrystallizedGrammarDependency

namespace InfoGeometry.Epistemology.CrystallizedGrammar.Tests

example :
    (1 / 2 : ℝ) ∈ convexHull ℝ ({0, 1} : Set ℝ) ∧
    (1 / 2 : ℝ) ∉ ({0, 1} : Set ℝ) ∧
    ∀ point ∈ convexHull ℝ ({0, 1} : Set ℝ),
      (0 : ℝ →ₗ[ℝ] ℝ) point ≤ (0 : ℝ →ₗ[ℝ] ℝ) (1 / 2) := by
  refine ⟨?_, by norm_num, ?_⟩
  · apply segment_subset_convexHull (by simp : (0 : ℝ) ∈ ({0, 1} : Set ℝ))
      (by simp : (1 : ℝ) ∈ ({0, 1} : Set ℝ))
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro point _
    simp

example : (1 : ℝ) ∈ ({0, 1} : Set ℝ) := by
  refine epistemic_crystallization ({0, 1} : Set ℝ) (LinearMap.id) 1 ?_ 1 ?_ rfl ?_
  · refine bound_on_convexHull ({0, 1} : Set ℝ) (fun point : ℝ => point)
      ⟨convex_convexHull ℝ _, fun _ _ _ _ _ _ _ _ _ => le_rfl⟩ 1 ?_
    intro point member
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl <;> norm_num
  · exact subset_convexHull ℝ _ (by simp)
  · intro point _ value
    exact value

example {Space : Type*} [AddCommGroup Space] [Module ℝ Space]
    (generators : Finset Space) (nonempty : generators.Nonempty) :
    ∃ optimum ∈ generators, ∀ point ∈ convexHull ℝ (↑generators : Set Space),
      (0 : ℝ) ≤ 0 := by
  exact finite_generator_maximum generators nonempty (fun _ => 0)
    ⟨convex_convexHull ℝ _, by intros; simp⟩

example : ¬ ∃ optimum : ℝ, optimum ∈ Set.Ioo 0 1 ∧
    ∀ point ∈ Set.Ioo 0 1, point ≤ optimum := by
  rintro ⟨optimum, member, maximal⟩
  have midpoint_mem : (optimum + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [member.1, member.2]
  have impossible := maximal ((optimum + 1) / 2) midpoint_mem
  linarith [member.2]

example (first second maximum weight : ℝ) (first_bound : first ≤ maximum)
    (second_bound : second ≤ maximum) (positive : 0 < weight) (below_one : weight < 1) :
    weight * first + (1 - weight) * second = maximum ↔
      first = maximum ∧ second = maximum := by
  exact linear_maximum_on_openSegment_iff (Set.Iic maximum) (LinearMap.id) maximum
    (fun _ member => member) first_bound second_bound
      ⟨weight, 1 - weight, positive, by linarith, by ring, rfl⟩

example : (0 : ℝ) * 0 + (1 - 0) * 1 = 1 ∧ (0 : ℝ) ≠ 1 := by
  norm_num

example : IsExtreme ℝ (Set.Icc (0 : ℝ) 1) {point ∈ Set.Icc (0 : ℝ) 1 | point = 1} := by
  exact maximizer_set_isExtreme ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).convexOn (convex_Icc 0 1))
    1 (fun _ member => member.2)

#print axioms maximizing_endpoints
#print axioms maximizer_set_isExtreme
#print axioms linear_maximum_on_openSegment_iff
#print axioms unique_maximizer_extreme
#print axioms unique_maximizer_mem_generators
#print axioms epistemic_crystallization
#print axioms bound_on_convexHull
#print axioms finite_generator_maximum
#print axioms ProofDependency.causal_branches
#print axioms ProofDependency.uniqueness_and_finiteness_incomparable
#print axioms ProofDependency.saturation_branches
#print axioms ProofDependency.no_cycle

end InfoGeometry.Epistemology.CrystallizedGrammar.Tests
