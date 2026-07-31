import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalRepresentationTransport

/-!
# Flow/representation intertwining on a filtered `TopCat` colimit

This is the categorical transport theorem needed to connect an existing
stagewise modular-flow colimit with a topological representation readout.
The stage covariance equation is explicit input; the global intertwiner then
follows solely from the colimit universal property.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationFlow

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable {B : Type u} [Semiring B] [Algebra ℂ B] [Star B]
variable [TopologicalSpace B]
variable (R : ContinuousStarRepresentationCocone
  (Stage := Stage) (sys := sys) (B := B))

/-- A source flow, a target flow, and their verified covariance on every
finite stage.  The source and target are only `TopCat` morphisms; no analytic
one-parameter-group law is assumed here. -/
structure Data where
  sourceFlow : ∀ t : ℝ,
    topologicalColimit Stage sys ⟶ topologicalColimit Stage sys
  targetFlow : ∀ t : ℝ, TopCat.of B ⟶ TopCat.of B

variable (D : Data (Stage := Stage) (sys := sys) (B := B))

/-- Stage covariance descends to the global representation intertwining law. -/
theorem representation_intertwines_flow
    (hcov : ∀ (t : ℝ) (i : I),
      topologicalInjection Stage sys i ≫ D.sourceFlow t ≫
          topologicalRepresentation Stage sys R =
        topologicalInjection Stage sys i ≫
          topologicalRepresentation Stage sys R ≫ D.targetFlow t)
    (t : ℝ) :
    D.sourceFlow t ≫ topologicalRepresentation Stage sys R =
      topologicalRepresentation Stage sys R ≫ D.targetFlow t := by
  apply colimit.hom_ext
  intro i
  exact hcov t i

@[reassoc]
theorem representation_intertwines_flow_assoc
    (hcov : ∀ (t : ℝ) (i : I),
      topologicalInjection Stage sys i ≫ D.sourceFlow t ≫
          topologicalRepresentation Stage sys R =
        topologicalInjection Stage sys i ≫
          topologicalRepresentation Stage sys R ≫ D.targetFlow t)
    (t : ℝ) (i : I) :
    topologicalInjection Stage sys i ≫ D.sourceFlow t ≫
        topologicalRepresentation Stage sys R =
      topologicalInjection Stage sys i ≫
        topologicalRepresentation Stage sys R ≫ D.targetFlow t := by
  exact hcov t i

end CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationFlow
