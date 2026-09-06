import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

/-- Chapter-local template for the paper's continuum-limit criterion. It stores the four
hypotheses used by the text and an abstract compactness extractor producing a weak limit
candidate. -/
theorem physical_spacetime_continuum_limit_extraction
    {Limit : Type} (convergesTo : Limit → Prop)
    (subadditiveControlled curvatureWeaklyCompact observerInvariant refinementCompatible : Prop)
    (weakCompactness :
      subadditiveControlled →
        curvatureWeaklyCompact →
          observerInvariant → refinementCompatible → ∃ limit, convergesTo limit)
    (hSubadditive : subadditiveControlled)
    (hCurvature : curvatureWeaklyCompact)
    (hObserver : observerInvariant)
    (hRefinement : refinementCompatible) :
    ∃ limit, convergesTo limit := by
  exact weakCompactness hSubadditive hCurvature hObserver hRefinement

/-- The continuum-limit template packages the four chapter hypotheses into a single abstract
compactness extraction, yielding a weak limit candidate.
    prop:physical-spacetime-continuum-limit-template -/
theorem paper_physical_spacetime_continuum_limit_template
    {Limit : Type} (convergesTo : Limit → Prop)
    (subadditiveControlled curvatureWeaklyCompact observerInvariant refinementCompatible : Prop)
    (weakCompactness :
      subadditiveControlled →
        curvatureWeaklyCompact →
          observerInvariant → refinementCompatible → ∃ limit, convergesTo limit)
    (hSubadditive : subadditiveControlled)
    (hCurvature : curvatureWeaklyCompact)
    (hObserver : observerInvariant)
    (hRefinement : refinementCompatible) :
    ∃ limit, convergesTo limit := by
  exact physical_spacetime_continuum_limit_extraction convergesTo
    subadditiveControlled curvatureWeaklyCompact observerInvariant refinementCompatible
    weakCompactness hSubadditive hCurvature hObserver hRefinement

end Omega.PhysicalSpacetimeSkeleton
