import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Topological colimit interface for filtered star-algebra systems

`ContinuousStarInductiveSystem` already carries continuous-linear transition
maps.  This file exposes those maps as a `TopCat` diagram and its categorical
colimit.  It is an interface for a supplied C⋆ tower; it does not assert a
concrete Cuntz realization or a norm completion of an algebraic quotient.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

def transitionContinuousMap {i j : I} (hij : i ≤ j) :
    ContinuousMap (Stage i) (Stage j) :=
  { toFun := sys.transitionCLM Stage hij
    continuous_toFun := (sys.transitionCLM Stage hij).continuous }

def topologicalDiagram : I ⥤ TopCat where
  obj i := TopCat.of (Stage i)
  map f := TopCat.ofHom (transitionContinuousMap Stage sys (leOfHom f))
  map_id i := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change sys.transitionCLM Stage (le_refl i) a = a
    rw [ContinuousStarInductiveSystem.transitionCLM_apply Stage sys,
      sys.map_id]
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change sys.transitionCLM Stage (le_trans (leOfHom f) (leOfHom g)) a =
      sys.transitionCLM Stage (leOfHom g)
        (sys.transitionCLM Stage (leOfHom f) a)
    rw [ContinuousStarInductiveSystem.transitionCLM_apply Stage sys,
      ContinuousStarInductiveSystem.transitionCLM_apply Stage sys,
      ContinuousStarInductiveSystem.transitionCLM_apply Stage sys]
    have h := congrArg (fun e => e a)
      (sys.map_comp (leOfHom f) (leOfHom g)).symm
    exact h

abbrev topologicalColimit : TopCat :=
  topologicalDirectColimit (topologicalDiagram Stage sys)

def topologicalInjection (i : I) :
    (topologicalDiagram Stage sys).obj i ⟶ topologicalColimit Stage sys :=
  topologicalDirectInjection (topologicalDiagram Stage sys) i

theorem topologicalInjection_transition
    {i j : I} (hij : i ≤ j) (a : Stage i) :
    topologicalInjection Stage sys j (sys.map hij a) =
      topologicalInjection Stage sys i a := by
  have h := (colimit.cocone (topologicalDiagram Stage sys)).w (homOfLE hij)
  simpa [topologicalInjection, topologicalDiagram,
    transitionContinuousMap] using congrArg (fun f => f a) h

end InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
