import InfoGeometry.Canonical.FilteredStarAlgebraAlgebraicToTopologicalColimit
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalStarReadout

/-!
# Topological transport of filtered star-algebra representations

This owner separates the algebraic representation cocone from its `TopCat`
readout.  Continuity of each observable-to-target map is explicit input; no
unavailable `CStarAlgebra` or analytic representation instance is fabricated.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraAlgebraicToTopologicalColimit
open CStarStateColimit.Native.FilteredStarAlgebraTopologicalStarReadout
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
variable [TopologicalSpace B] [ContinuousStar B]

def continuousStarTopCatHom : TopCat.of B ⟶ TopCat.of B :=
  TopCat.ofHom
    { toFun := star
      continuous_toFun := ContinuousStar.continuous_star }

/-- A compatible star-algebra representation cocone whose individual maps
are known to be continuous in the chosen target topology. -/
structure ContinuousStarRepresentationCocone where
  ι : ∀ i, Stage i →⋆ₐ[ℂ] B
  ι_comm : ∀ {i j : I} (hij : i ≤ j),
    (ι j).comp (sys.map hij) = ι i
  continuous_ι : ∀ i, Continuous (ι i)

variable (R : ContinuousStarRepresentationCocone
  (Stage := Stage) (sys := sys) (B := B))

def algebraicRepresentation :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B :=
  liftStarAlgHom Stage sys R.ι (fun hij x =>
    congrArg (fun g : Stage _ →⋆ₐ[ℂ] B => g x) (R.ι_comm hij))

def topologicalRepresentationCocone :
    Cocone (topologicalDiagram Stage sys) where
  pt := TopCat.of B
  ι :=
    { app := fun i =>
        TopCat.ofHom
          { toFun := R.ι i
            continuous_toFun := R.continuous_ι i }
      naturality := by
        intro i j f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        change R.ι j (sys.map (leOfHom f) x) = R.ι i x
        exact congrArg (fun g : Stage i →⋆ₐ[ℂ] B => g x)
          (R.ι_comm (leOfHom f)) }

noncomputable def topologicalRepresentation :
    topologicalColimit Stage sys ⟶ TopCat.of B :=
  topologicalDirectDescend (topologicalDiagram Stage sys)
    (topologicalRepresentationCocone Stage sys R)

@[simp] theorem algebraicRepresentation_of_stage
    (i : I) (x : Stage i) :
    algebraicRepresentation Stage sys R
        (algebraicStarDirectLimitOf Stage sys i x) = R.ι i x := by
  exact liftStarAlgHom_of Stage sys R.ι (fun hij x =>
    congrArg (fun g : Stage _ →⋆ₐ[ℂ] B => g x) (R.ι_comm hij)) i x

@[simp] theorem topologicalRepresentation_of_stage
    (i : I) (x : Stage i) :
    topologicalRepresentation Stage sys R
        (topologicalInjection Stage sys i x) = R.ι i x := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram Stage sys)
    (topologicalRepresentationCocone Stage sys R) i
  exact congrArg (fun f => f x) h

theorem topologicalRepresentation_star_intertwines :
    topologicalStarReadout Stage sys ≫
        topologicalRepresentation Stage sys R =
      topologicalRepresentation Stage sys R ≫
        continuousStarTopCatHom (B := B) := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change topologicalRepresentation Stage sys R
      (topologicalStarReadout Stage sys
        (topologicalInjection Stage sys i x)) =
    star (topologicalRepresentation Stage sys R
      (topologicalInjection Stage sys i x))
  rw [topologicalStarReadout_stage]
  rw [topologicalRepresentation_of_stage]
  rw [topologicalRepresentation_of_stage]
  change R.ι i (star x) = star (R.ι i x)
  exact map_star (R.ι i) x

theorem topologicalRepresentation_comp_algebraicToTopological
    (x : AlgebraicStarDirectLimit Stage sys) :
    topologicalRepresentation Stage sys R
        (algebraicToTopological Stage sys x) =
      algebraicRepresentation Stage sys R x := by
  induction x using _root_.DirectLimit.induction with
  | _ i a =>
      change topologicalRepresentation Stage sys R
          (algebraicToTopological Stage sys
            (algebraicStarDirectLimitOf Stage sys i a)) =
        algebraicRepresentation Stage sys R
          (algebraicStarDirectLimitOf Stage sys i a)
      rw [algebraicToTopological_of_stage,
        topologicalRepresentation_of_stage,
        algebraicRepresentation_of_stage]

theorem algebraicRepresentation_unique
    (F : AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B)
    (hF : ∀ i,
      F.comp (algebraicStarDirectLimitOf Stage sys i) = R.ι i) :
    F = algebraicRepresentation Stage sys R := by
  apply liftStarAlgHom_unique Stage sys R.ι
    (fun hij x =>
      congrArg (fun g : Stage _ →⋆ₐ[ℂ] B => g x) (R.ι_comm hij)) F hF

theorem topologicalRepresentation_unique
    (f : topologicalColimit Stage sys ⟶ TopCat.of B)
    (hf : ∀ (i : I) (x : Stage i),
      f (topologicalInjection Stage sys i x) = R.ι i x) :
    f = topologicalRepresentation Stage sys R := by
  apply topologicalDirectDescend_unique
    (topologicalDiagram Stage sys)
    (topologicalRepresentationCocone Stage sys R) f
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change f (topologicalInjection Stage sys i x) = R.ι i x
  exact hf i x

end CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport
