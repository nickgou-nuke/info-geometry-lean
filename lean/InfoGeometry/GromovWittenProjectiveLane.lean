import Mathlib.Logic.Nonempty
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical Gromov--Witten projective lane surface

This file avoids packet/correspondence structures.  It records only the direct
logical content that explicitly supplied relation witnesses make the combined
relation type nonempty.  No Gromov--Witten invariant, localization formula,
quantum metric convergence theorem, Langlands correspondence, or analytic
geometry theorem is asserted.
-/

noncomputable section

namespace InfoGeometry

namespace GromovWittenProjectiveLane

/--
Explicit relation witnesses for the projective/GW/operator-metric chain produce
an inhabitant of the product relation type.
-/
theorem constructErlangenLanglandsGromovLaneTarget
    (LanglandsProjectiveRelation ProjectiveGWRelation GWMetricRelation
      LanglandsMetricRelation : Type*)
    (lp : LanglandsProjectiveRelation)
    (pg : ProjectiveGWRelation)
    (gm : GWMetricRelation)
    (lm : LanglandsMetricRelation) :
    Nonempty
      (LanglandsProjectiveRelation × ProjectiveGWRelation ×
        GWMetricRelation × LanglandsMetricRelation) := by
  exact ⟨(lp, pg, gm, lm)⟩

/-- A supplied full-chain witness remains a supplied full-chain witness. -/
theorem constructErlangenLanglandsGWFromExplicitProduct
    (LanglandsProjectiveRelation ProjectiveGWRelation GWMetricRelation
      LanglandsMetricRelation : Type*)
    (chain : LanglandsProjectiveRelation × ProjectiveGWRelation ×
      GWMetricRelation × LanglandsMetricRelation) :
    Nonempty
      (LanglandsProjectiveRelation × ProjectiveGWRelation ×
        GWMetricRelation × LanglandsMetricRelation) := by
  exact ⟨chain⟩

end GromovWittenProjectiveLane

end InfoGeometry
