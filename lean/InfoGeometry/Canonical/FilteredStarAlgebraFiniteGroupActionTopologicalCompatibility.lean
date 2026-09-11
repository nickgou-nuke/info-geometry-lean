import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimitTopologicalRealization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredStarAlgebraFiniteGroupActionEquivDirectLimit

/-!
# Stagewise compatibility of finite-group star actions with topological realizations

This owner compares a descended finite-group `StarAlgEquiv` on the algebraic
direct limit with a supplied topological realization target.  It does not
manufacture a new topology or quotient carrier.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionTopologicalCompatibility

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionEquivDirectLimit

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarGroupAction I G Stage sys)
variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A topological realization target equipped with a finite-group action. -/
structure CompatibleTopologicalGroupAction
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B)) where
  action : G → B →⋆ₐ[ℂ] B
  stage_agreement : ∀ (i : I) (g : G),
    (action g).comp (R.ι i) = (R.ι i).comp (A.action i g)

variable (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
variable (T : CompatibleTopologicalGroupAction Stage sys A R)

theorem topologicalGroupAction_on_stage
    (i : I) (g : G) (x : Stage i) :
    T.action g (R.ι i x) = R.ι i (A.action i g x) := by
  exact congrArg (fun f : Stage i →⋆ₐ[ℂ] B => f x)
    (T.stage_agreement i g)

theorem topologicalGroupAction_agrees_with_algebraicAction_on_stage
    (i : I) (g : G) (x : Stage i) :
    T.action g
        (algebraicDescend Stage sys R
          (algebraicStarDirectLimitOf Stage sys i x)) =
      algebraicDescend Stage sys R
        (algebraicColimitGroupAction I G Stage sys A g
          (algebraicStarDirectLimitOf Stage sys i x)) := by
  rw [algebraicDescend_of, algebraicColimitGroupAction_on_stage,
    algebraicDescend_of]
  exact topologicalGroupAction_on_stage Stage sys A R T i g x

theorem topologicalGroupAction_agrees_with_algebraicEquiv_on_stage
    (i : I) (g : G) (x : Stage i) :
    T.action g
        (algebraicDescend Stage sys R
          (algebraicStarDirectLimitOf Stage sys i x)) =
      algebraicDescend Stage sys R
        (algebraicColimitGroupActionEquiv Stage sys A g
          (algebraicStarDirectLimitOf Stage sys i x)) := by
  simpa [algebraicColimitGroupActionEquiv_apply] using
    topologicalGroupAction_agrees_with_algebraicAction_on_stage
      Stage sys A R T i g x

end CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionTopologicalCompatibility
