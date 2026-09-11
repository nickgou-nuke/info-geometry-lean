import InfoGeometry.Canonical.FilteredStarAlgebraActionEquivDirectLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimitTopologicalCompatibility

/-!
# Stagewise compatibility of algebraic and topological star actions

The algebraic direct limit and a supplied topological realization are distinct
carriers.  This owner records the precise compatibility datum needed to
compare their actions on finite-stage representatives.  It does not identify
the two carriers and does not manufacture a topology or a completion on the
algebraic direct limit.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredStarAlgebraActionTopologicalCompatibility

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraActionDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraActionEquivDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarAction Stage sys)
variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A topological action is supplied explicitly on the realization target.
The stage equation is the only bridge between the two carriers. -/
structure CompatibleTopologicalAction
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    where
  action : ℤ → B →⋆ₐ[ℂ] B
  stage_agreement : ∀ (i : I) (t : ℤ),
    (action t).comp (R.ι i) = (R.ι i).comp (A.action i t)

variable (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
variable (T : CompatibleTopologicalAction Stage sys A R)

theorem topologicalAction_on_stage (i : I) (t : ℤ) (x : Stage i) :
    T.action t (R.ι i x) = R.ι i (A.action i t x) := by
  exact congrArg (fun f : Stage i →⋆ₐ[ℂ] B => f x)
    (T.stage_agreement i t)

theorem topologicalAction_agrees_with_algebraicAction_on_stage
    (i : I) (t : ℤ) (x : Stage i) :
    T.action t
        (algebraicDescend Stage sys R
          (algebraicStarDirectLimitOf Stage sys i x)) =
      algebraicDescend Stage sys R
        (algebraicColimitAction Stage sys A t
          (algebraicStarDirectLimitOf Stage sys i x)) := by
  rw [algebraicDescend_of, algebraicColimitAction_on_stage,
    algebraicDescend_of]
  exact (topologicalAction_on_stage Stage sys A R T i t x)

theorem topologicalAction_agrees_with_algebraicEquiv_on_stage
    (i : I) (t : ℤ) (x : Stage i) :
    T.action t
        (algebraicDescend Stage sys R
          (algebraicStarDirectLimitOf Stage sys i x)) =
      algebraicDescend Stage sys R
        (algebraicColimitActionEquiv Stage sys A t
          (algebraicStarDirectLimitOf Stage sys i x)) := by
  simpa [algebraicColimitActionEquiv_apply] using
    topologicalAction_agrees_with_algebraicAction_on_stage
      Stage sys A R T i t x

end CStarStateColimit.Native.FilteredStarAlgebraActionTopologicalCompatibility
