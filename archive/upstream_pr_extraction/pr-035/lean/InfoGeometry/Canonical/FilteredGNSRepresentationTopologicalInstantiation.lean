import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalRepresentationTransport
import InfoGeometry.Canonical.FilteredGNSAlgebraicColimitRepresentation

/-!
# GNS specialization of the topological representation transport

The generic representation cocone is instantiated for the global filtered GNS
bounded-operator carrier.  Continuity of the observable-to-operator maps is
kept as explicit data: this is the exact remaining analytic/topological input,
not a hidden instance or an ax!om.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredGNSRepresentationTopologicalInstantiation

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSGlobalRepresentationCompatibility
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

abbrev GNSOperator : Type u :=
  GNSHilbertColimit Stage sys ω →L[ℂ]
    GNSHilbertColimit Stage sys ω

variable [ContinuousStar (GNSOperator Stage sys ω)]

/-- The only extra datum needed to place the GNS representation in `TopCat`:
continuity of each stage representation as a map into bounded operators. -/
structure Data where
  continuous_stage : ∀ i : I,
    Continuous (globalStageRepresentationStarAlgHom Stage sys ω i)

variable (D : Data Stage sys ω)

def representationCocone :
    ContinuousStarRepresentationCocone
      (Stage := Stage) (sys := sys) (B := GNSOperator Stage sys ω) where
  ι := fun i => globalStageRepresentationStarAlgHom Stage sys ω i

def representationCocone_comm :
    ∀ {i j : I} (hij : i ≤ j),
      ((representationCocone Stage sys ω).ι j).comp (sys.map hij) =
        (representationCocone Stage sys ω).ι i := by
    intro i j hij
    apply DFunLike.ext _ _
    intro a
    exact globalStageRepresentation_transition Stage sys ω hij a

def representationCocone_continuous :
    ∀ i : I, Continuous ((representationCocone Stage sys ω).ι i) :=
  D.continuous_stage

noncomputable def topologicalRepresentation :
    topologicalColimit Stage sys ⟶
      TopCat.of (GNSOperator Stage sys ω) :=
  CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport.topologicalRepresentation
    Stage sys (representationCocone Stage sys ω)
    (representationCocone_comm Stage sys ω)
    (representationCocone_continuous Stage sys ω D)

@[simp] theorem topologicalRepresentation_stage
    (i : I) (a : Stage i) :
    topologicalRepresentation Stage sys ω D
        (topologicalInjection Stage sys i a) =
      globalStageRepresentationStarAlgHom Stage sys ω i a := by
  exact CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport.topologicalRepresentation_of_stage Stage sys
    (representationCocone Stage sys ω)
    (representationCocone_comm Stage sys ω)
    (representationCocone_continuous Stage sys ω D) i a

theorem topologicalRepresentation_factorization
    (x : AlgebraicStarDirectLimit Stage sys) :
    topologicalRepresentation Stage sys ω D
        (FilteredStarAlgebraAlgebraicToTopologicalColimit.algebraicToTopological
          Stage sys x) =
      algebraicColimitGNSRepresentation Stage sys ω x := by
  exact CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport.topologicalRepresentation_comp_algebraicToTopological Stage sys
    (representationCocone Stage sys ω)
    (representationCocone_comm Stage sys ω)
    (representationCocone_continuous Stage sys ω D) x

end CStarStateColimit.Native.FilteredGNSRepresentationTopologicalInstantiation
