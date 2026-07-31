import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimit
import InfoGeometry.Canonical.FilteredStarInductiveCoconeTopCat

/-!
# Topological realizations of the noncommutative star direct limit

The algebraic direct limit has no topology by default.  This file therefore
does not manufacture one.  Instead it packages an explicitly supplied
continuous star-algebra cocone and exposes both universal descents:
the algebraic `StarAlgHom` and the categorical `TopCat` colimit map.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.ContinuousStarInductiveSystem
open CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A topological realization is data, not an existence theorem: each finite
stage is sent continuously into a chosen target and the maps satisfy the
filtered cocone law. -/
structure TopologicalRealization
    (sys : ContinuousStarInductiveSystem Stage) where
  ι : ∀ i, Stage i →⋆ₐ[ℂ] B

def toStarInductiveCocone
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (R.ι j).comp (sys.map hij) = R.ι i) :
    ContinuousStarInductiveSystem.StarInductiveCocone
      (Ainf := B) Stage sys where
  ι := R.ι
  ι_comm := hι_comm

def algebraicDescend
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (R.ι j).comp (sys.map hij) = R.ι i) :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B :=
  liftStarAlgHom Stage sys R.ι (fun hij x =>
    congrArg (fun g : Stage _ →⋆ₐ[ℂ] B => g x) (hι_comm hij))

@[simp] theorem algebraicDescend_of
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (R.ι j).comp (sys.map hij) = R.ι i)
    (i : I) (x : Stage i) :
    algebraicDescend Stage sys R hι_comm
        (algebraicStarDirectLimitOf Stage sys i x) = R.ι i x := by
  exact liftStarAlgHom_of Stage sys R.ι (fun hij x =>
    congrArg (fun g : Stage _ →⋆ₐ[ℂ] B => g x) (hι_comm hij)) i x

def topologicalCocone
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (R.ι j).comp (sys.map hij) = R.ι i) :
    StarInductiveCocone (Ainf := B) Stage sys :=
  toStarInductiveCocone Stage sys R hι_comm

noncomputable def topologicalColimitMap
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (R.ι j).comp (sys.map hij) = R.ι i) :
    topologicalColimit Stage sys ⟶ TopCat.of B :=
  toTopologicalColimitMap sys (topologicalCocone Stage sys R hι_comm)

theorem topologicalColimitMap_inclusion
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (R.ι j).comp (sys.map hij) = R.ι i)
    (i : I) (x : Stage i) :
    topologicalColimitMap Stage sys R hι_comm
        (topologicalInjection Stage sys i x) = R.ι i x := by
  exact toTopologicalColimitMap_inclusion sys
    (topologicalCocone Stage sys R hι_comm) i x

theorem topologicalColimitMap_continuous_stage
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (hcontinuous_ι : ∀ i, Continuous (R.ι i)) (i : I) :
    Continuous (R.ι i) :=
  hcontinuous_ι i

end CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization
