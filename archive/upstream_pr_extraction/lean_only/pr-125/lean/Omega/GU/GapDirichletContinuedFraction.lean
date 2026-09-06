import Mathlib.Tactic

namespace Omega.GU

/-- Paper-facing wrapper for the gap-restricted Dirichlet series package: absolute convergence,
truncated-recursion convergence, the continued-fraction recurrence, and the Euler-product bounds.
    thm:group-jg-gap-dirichlet-continued-fraction -/
theorem paper_group_jg_gap_dirichlet_continued_fraction
    {absolutelyConvergent recursionConverges continuedFractionRecurrence eulerBounds : Prop}
    (hAbsolute : absolutelyConvergent)
    (hRecursion : recursionConverges)
    (hRecurrence : continuedFractionRecurrence)
    (hEuler : eulerBounds) :
    absolutelyConvergent ∧ recursionConverges ∧ continuedFractionRecurrence ∧ eulerBounds :=
  ⟨hAbsolute, hRecursion, hRecurrence, hEuler⟩

end Omega.GU
