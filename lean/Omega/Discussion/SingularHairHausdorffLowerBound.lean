import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace Omega.Discussion

/-- Inclusion of the singular support in the nonanalytic set and monotonicity of the dimension
functional give the claimed lower bound. -/
theorem paper_discussion_singular_hair_hausdorff_lower_bound
    {α : Type} (singularSupport nonanalyticSet : Set α) (dimH : Set α → ℝ)
    (singularSupport_subset_nonanalytic : singularSupport ⊆ nonanalyticSet)
    (dimH_mono : Monotone dimH) :
    singularSupport ⊆ nonanalyticSet ∧
      dimH singularSupport ≤ dimH nonanalyticSet := by
  exact ⟨singularSupport_subset_nonanalytic,
    dimH_mono singularSupport_subset_nonanalytic⟩

end Omega.Discussion
