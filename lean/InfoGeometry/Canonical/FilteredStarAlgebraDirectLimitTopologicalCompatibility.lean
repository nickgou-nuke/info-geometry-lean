import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimitTopologicalRealization
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compatibility of algebraic and topological star-colimit readouts

The algebraic direct limit and the categorical `TopCat` colimit are distinct
owners.  A supplied topological realization gives one descent in each lane;
this theorem records that their finite-stage evaluations agree exactly.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalCompatibility

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem algebraicDescend_eq_topologicalColimitMap_on_stage
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (i : I) (x : Stage i) :
    algebraicDescend Stage sys R
        (algebraicStarDirectLimitOf Stage sys i x) =
      topologicalColimitMap Stage sys R
        (topologicalInjection Stage sys i x) := by
  rw [algebraicDescend_of, topologicalColimitMap_inclusion]

end CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalCompatibility
