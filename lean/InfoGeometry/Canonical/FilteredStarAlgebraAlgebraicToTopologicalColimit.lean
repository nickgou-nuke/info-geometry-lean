import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimitTopologicalCompatibility
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic-to-topological filtered star-colimit comparison

The algebraic direct limit and the `TopCat` colimit are separate carriers.
This file supplies the canonical map from the former to the latter, and proves
that every supplied topological realization factors through it.  No topology
is put on the algebraic quotient by this construction.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredStarAlgebraAlgebraicToTopologicalColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalCompatibility
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

/-- The canonical carrier map from the algebraic filtered quotient to the
categorical `TopCat` colimit.  It is defined by the universal property of the
explicit algebraic direct limit and uses the topological injections as its
stage cocone. -/
noncomputable def algebraicToTopological :
    AlgebraicStarDirectLimit Stage sys →
      topologicalColimit Stage sys :=
  _root_.DirectLimit.lift
    (fun _ _ hij => starTransition Stage sys hij)
    (fun i => topologicalInjection Stage sys i)
    (by
      intro i j hij x
      exact (topologicalInjection_transition Stage sys hij x).symm)

@[simp] theorem algebraicToTopological_of_stage
    (i : I) (x : Stage i) :
    algebraicToTopological Stage sys
        (algebraicStarDirectLimitOf Stage sys i x) =
      topologicalInjection Stage sys i x := by
  rfl

/-- The topological readout of the canonical comparison map agrees with the
algebraic descent on every element of the algebraic direct limit. -/
theorem topologicalColimitMap_comp_algebraicToTopological
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (x : AlgebraicStarDirectLimit Stage sys) :
    topologicalColimitMap Stage sys R
        (algebraicToTopological Stage sys x) =
      algebraicDescend Stage sys R x := by
  induction x using _root_.DirectLimit.induction with
  | _ i a =>
      change topologicalColimitMap Stage sys R
          (algebraicToTopological Stage sys
            (algebraicStarDirectLimitOf Stage sys i a)) =
        algebraicDescend Stage sys R
          (algebraicStarDirectLimitOf Stage sys i a)
      rw [algebraicToTopological_of_stage,
        topologicalColimitMap_inclusion,
        algebraicDescend_of]

end CStarStateColimit.Native.FilteredStarAlgebraAlgebraicToTopologicalColimit
