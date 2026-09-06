import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit
import InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalTransitions

/-!
# Filtered topological colimit of the finite D₄-star crossed-product transitions

The transition system already supplies continuous coefficientwise crossed-product
maps.  This file packages those maps into a filtered `TopCat` diagram and
records the universal stage equation for the resulting colimit.

No quotient collapse or completion theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalColimit

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalTransitions

universe u

variable {I : Type u} [Preorder I]
variable (T : ContinuousD4StarCrossedProductTransitionSystem I)

def topologicalDiagram : I ⥤ TopCat where
  obj _ := TopCat.of D4StarCrossedProduct
  map f := T.transitionTopCatHom (leOfHom f)
  map_id i := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro F
    simpa using congrArg (fun h => h F) (T.transitionTopCatHom_refl i)
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro F
    simpa using congrArg (fun h => h F)
      (T.transitionTopCatHom_trans (leOfHom f) (leOfHom g))

variable (C : Cocone (topologicalDiagram T))
variable (hC : IsColimit C)

abbrev topologicalColimit : TopCat :=
  C.pt

def topologicalInjection (i : I) :
    TopCat.of D4StarCrossedProduct ⟶ topologicalColimit T C :=
  C.ι.app i

@[reassoc (attr := simp)]
theorem topologicalInjection_transition_hom
    {i j : I} (hij : i ≤ j) :
    T.transitionTopCatHom hij ≫ topologicalInjection T C j =
      topologicalInjection T C i := by
  exact C.w (homOfLE hij)

theorem topologicalInjection_transition
    {i j : I} (hij : i ≤ j) (F : D4StarCrossedProduct) :
    topologicalInjection T C j (T.transitionTopCatHom hij F) =
      topologicalInjection T C i F := by
  exact congrArg (fun h => h F)
    (topologicalInjection_transition_hom (T := T) (C := C) hij)

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalColimit
