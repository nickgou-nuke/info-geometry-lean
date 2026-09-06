import InfoGeometry.Canonical.FilteredStarAlgebraActionTopologicalCompatibility

/-!
# Stagewise compatibility for topological `StarAlgEquiv` actions

The algebraic direct-limit action is packaged as a `StarAlgEquiv`, while a
topological realization lives on a separately supplied target carrier.  This
owner records their agreement on every finite-stage image.  It deliberately
does not identify the two carriers or infer a completion.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredStarAlgebraActionEquivTopologicalCompatibility

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

structure CompatibleTopologicalEquivAction
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B)) where
  action : ℤ → B ≃⋆ₐ[ℂ] B
  stage_agreement : ∀ (i : I) (t : ℤ),
    ∀ x, action t (R.ι i x) = R.ι i (A.action i t x)

variable (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
variable (T : CompatibleTopologicalEquivAction Stage sys A R)

theorem topologicalEquivAction_on_stage (i : I) (t : ℤ) (x : Stage i) :
    T.action t (R.ι i x) = R.ι i (A.action i t x) := by
  exact T.stage_agreement i t x

theorem topologicalEquivAction_agrees_with_algebraicEquiv_on_stage
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (R.ι j).comp (sys.map hij) = R.ι i)
    (i : I) (t : ℤ) (x : Stage i) :
    T.action t
        (algebraicDescend Stage sys R hι_comm
          (algebraicStarDirectLimitOf Stage sys i x)) =
      algebraicDescend Stage sys R hι_comm
        (algebraicColimitActionEquiv Stage sys A t
          (algebraicStarDirectLimitOf Stage sys i x)) := by
  rw [algebraicDescend_of, algebraicColimitActionEquiv_apply,
    algebraicColimitAction_on_stage, algebraicDescend_of]
  exact topologicalEquivAction_on_stage Stage sys A R T i t x

end CStarStateColimit.Native.FilteredStarAlgebraActionEquivTopologicalCompatibility
