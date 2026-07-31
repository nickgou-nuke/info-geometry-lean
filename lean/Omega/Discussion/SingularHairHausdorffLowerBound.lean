import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace Omega.Discussion

/-- Carrier data for the Hausdorff-dimension monotonicity argument. -/
structure SingularHairHausdorffLowerBoundData where
  α : Type
  singularSupport : Set α
  nonanalyticSet : Set α
  dimH : Set α → ℝ

/-- Inclusion of the singular support in the nonanalytic set and monotonicity of the dimension
functional give the claimed lower bound. -/
theorem paper_discussion_singular_hair_hausdorff_lower_bound
    (D : SingularHairHausdorffLowerBoundData)
    (singularSupport_subset_nonanalytic : D.singularSupport ⊆ D.nonanalyticSet)
    (dimH_mono : Monotone D.dimH) :
    D.singularSupport ⊆ D.nonanalyticSet ∧
      D.dimH D.singularSupport ≤ D.dimH D.nonanalyticSet := by
  exact ⟨singularSupport_subset_nonanalytic,
    dimH_mono singularSupport_subset_nonanalytic⟩

end Omega.Discussion
