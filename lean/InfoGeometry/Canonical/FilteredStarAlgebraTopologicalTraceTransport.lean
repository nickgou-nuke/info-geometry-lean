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

variable (T : CyclicTraceRealization (Stage := Stage) (sys := sys) (B := B))

/-- The scalar trace descended through the algebraic star-colimit. -/
def algebraicTrace
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (T.realization.ι j).comp (sys.map hij) = T.realization.ι i) :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B :=
  algebraicDescend Stage sys T.realization hι_comm

/-- The scalar trace readout on the categorical `TopCat` colimit. -/
noncomputable def topologicalTrace
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (T.realization.ι j).comp (sys.map hij) = T.realization.ι i) :
    topologicalColimit Stage sys ⟶ TopCat.of B :=
  topologicalColimitMap Stage sys T.realization hι_comm

@[simp] theorem algebraicTrace_of_stage
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (T.realization.ι j).comp (sys.map hij) = T.realization.ι i)
    (i : I) (x : Stage i) :
    algebraicTrace Stage sys T hι_comm
        (algebraicStarDirectLimitOf Stage sys i x) =
      T.realization.ι i x := by
  exact algebraicDescend_of Stage sys T.realization hι_comm i x

theorem algebraicTrace_cyclic
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (T.realization.ι j).comp (sys.map hij) = T.realization.ι i)
    (hcyclic : ∀ (i : I) (x y : Stage i),
      T.realization.ι i (x * y) = T.realization.ι i (y * x))
    (x y : AlgebraicStarDirectLimit Stage sys) :
    algebraicTrace Stage sys T hι_comm (x * y) =
      algebraicTrace Stage sys T hι_comm (y * x) := by
  induction x, y using _root_.DirectLimit.induction₂ with
  | _ i a b =>
      rw [DirectLimit.mul_def, DirectLimit.mul_def]
      change T.realization.ι i (a * b) = T.realization.ι i (b * a)
      exact hcyclic i a b

@[simp] theorem topologicalTrace_of_stage
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (T.realization.ι j).comp (sys.map hij) = T.realization.ι i)
    (i : I) (x : Stage i) :
    topologicalTrace Stage sys T hι_comm
        (topologicalInjection Stage sys i x) =
      T.realization.ι i x := by
  exact topologicalColimitMap_inclusion Stage sys T.realization hι_comm i x

theorem topologicalTrace_comp_algebraicToTopological
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (T.realization.ι j).comp (sys.map hij) = T.realization.ι i)
    (x : AlgebraicStarDirectLimit Stage sys) :
    topologicalTrace Stage sys T hι_comm
        (algebraicToTopological Stage sys x) =
      algebraicTrace Stage sys T hι_comm x := by
  exact topologicalColimitMap_comp_algebraicToTopological
    Stage sys T.realization hι_comm x

/- The algebraic trace is the unique star-algebra descent with the supplied
finite-stage trace values. -/
theorem algebraicTrace_unique
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (T.realization.ι j).comp (sys.map hij) = T.realization.ι i)
    (F : AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B)
    (hF : ∀ i,
      F.comp (algebraicStarDirectLimitOf Stage sys i) = T.realization.ι i) :
    F = algebraicTrace Stage sys T hι_comm := by
  change F = algebraicDescend Stage sys T.realization hι_comm
  apply liftStarAlgHom_unique
    Stage sys T.realization.ι
    (fun hij x =>
      congrArg (fun g : Stage _ →⋆ₐ[ℂ] B => g x)
        (hι_comm hij))
    F hF

/- The TopCat trace readout is the unique continuous colimit morphism with
the supplied finite-stage values. -/
theorem topologicalTrace_unique
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (T.realization.ι j).comp (sys.map hij) = T.realization.ι i)
    (f : topologicalColimit Stage sys ⟶ TopCat.of B)
    (hf : ∀ (i : I) (x : Stage i),
      f (topologicalInjection Stage sys i x) = T.realization.ι i x) :
    f = topologicalTrace Stage sys T hι_comm := by
  change f = topologicalColimitMap Stage sys T.realization hι_comm
  apply FilteredColimit.Native.Topological.topologicalDirectDescend_unique
    (topologicalDiagram Stage sys)
    (toTopCatCocone sys (topologicalCocone Stage sys T.realization hι_comm)) f
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change f (topologicalInjection Stage sys i x) = T.realization.ι i x
  exact hf i x

end CStarStateColimit.Native.FilteredStarAlgebraTopologicalTraceTransport
