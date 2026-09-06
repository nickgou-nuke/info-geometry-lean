import Mathlib.Tactic

namespace Omega.Discussion

/-- Paper-facing wrapper for the Squier-curvature/discrete-Stokes package: the curvature cocycle
is closed, the chain/cochain pairing satisfies discrete Stokes, and holonomy along a boundary is
therefore controlled by the curvature filling term.
    prop:discussion-squier-curvature-holonomy-stokes -/
theorem paper_discussion_squier_curvature_holonomy_stokes
    (curvatureIsCocycle discreteStokes holonomyControlled : Prop)
    (hCocycle : curvatureIsCocycle) (hStokes : discreteStokes)
    (hHol : curvatureIsCocycle ∧ discreteStokes → holonomyControlled) :
    curvatureIsCocycle ∧ discreteStokes ∧ holonomyControlled := by
  exact ⟨hCocycle, hStokes, hHol ⟨hCocycle, hStokes⟩⟩

end Omega.Discussion
