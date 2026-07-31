import InfoGeometry.Canonical.FilteredStarAlgebraAlgebraicToTopologicalColimit

/-!
# Cyclic trace transport through a filtered star-colimit

This owner packages a supplied family of continuous, cyclic finite-stage
functionals into the two existing colimit lanes. It proves only what the data
support: algebraic descent, topological readout, and cyclicity on the
algebraic quotient. A Markov stabilization law is deliberately not inferred.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredStarAlgebraTopologicalTraceTransport

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization
open CStarStateColimit.Native.FilteredStarAlgebraAlgebraicToTopologicalColimit
open CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone
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

/-- A compatible continuous family of scalar-valued stage traces, with the
cyclic law made explicit at each noncommutative stage. -/
structure CyclicTraceRealization where
  realization : TopologicalRealization (Stage := Stage) (sys := sys) (B := B)
  cyclic : ∀ (i : I) (x y : Stage i),
    realization.ι i (x * y) = realization.ι i (y * x)

variable (T : CyclicTraceRealization (Stage := Stage) (sys := sys) (B := B))

/-- The scalar trace descended through the algebraic star-colimit. -/
def algebraicTrace :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B :=
  algebraicDescend Stage sys T.realization

/-- The scalar trace readout on the categorical `TopCat` colimit. -/
noncomputable def topologicalTrace :
    topologicalColimit Stage sys ⟶ TopCat.of B :=
  topologicalColimitMap Stage sys T.realization

@[simp] theorem algebraicTrace_of_stage
    (i : I) (x : Stage i) :
    algebraicTrace Stage sys T
        (algebraicStarDirectLimitOf Stage sys i x) =
      T.realization.ι i x := by
  exact algebraicDescend_of Stage sys T.realization i x

theorem algebraicTrace_cyclic
    (x y : AlgebraicStarDirectLimit Stage sys) :
    algebraicTrace Stage sys T (x * y) =
      algebraicTrace Stage sys T (y * x) := by
  induction x, y using _root_.DirectLimit.induction₂ with
  | _ i a b =>
      rw [DirectLimit.mul_def, DirectLimit.mul_def]
      change T.realization.ι i (a * b) = T.realization.ι i (b * a)
      exact T.cyclic i a b

@[simp] theorem topologicalTrace_of_stage
    (i : I) (x : Stage i) :
    topologicalTrace Stage sys T
        (topologicalInjection Stage sys i x) =
      T.realization.ι i x := by
  exact topologicalColimitMap_inclusion Stage sys T.realization i x

theorem topologicalTrace_comp_algebraicToTopological
    (x : AlgebraicStarDirectLimit Stage sys) :
    topologicalTrace Stage sys T
        (algebraicToTopological Stage sys x) =
      algebraicTrace Stage sys T x := by
  exact topologicalColimitMap_comp_algebraicToTopological
    Stage sys T.realization x

/- The algebraic trace is the unique star-algebra descent with the supplied
finite-stage trace values. -/
theorem algebraicTrace_unique
    (F : AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B)
    (hF : ∀ i,
      F.comp (algebraicStarDirectLimitOf Stage sys i) = T.realization.ι i) :
    F = algebraicTrace Stage sys T := by
  apply liftStarAlgHom_unique
    Stage sys T.realization.ι
    (fun hij x =>
      congrArg (fun g : Stage _ →⋆ₐ[ℂ] B => g x)
        (T.realization.ι_comm hij))
    F hF

/- The TopCat trace readout is the unique continuous colimit morphism with
the supplied finite-stage values. -/
theorem topologicalTrace_unique
    (f : topologicalColimit Stage sys ⟶ TopCat.of B)
    (hf : ∀ (i : I) (x : Stage i),
      f (topologicalInjection Stage sys i x) = T.realization.ι i x) :
    f = topologicalTrace Stage sys T := by
  apply FilteredColimit.Native.Topological.topologicalDirectDescend_unique
    (topologicalDiagram Stage sys)
    (toTopCatCocone sys (topologicalCocone Stage sys T.realization)) f
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change f (topologicalInjection Stage sys i x) = T.realization.ι i x
  exact hf i x

end CStarStateColimit.Native.FilteredStarAlgebraTopologicalTraceTransport
