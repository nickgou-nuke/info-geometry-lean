import InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProductTopCat
import InfoGeometry.OperatorAlgebra.D4StarCrossedProductTransitions

/-!
# Topological realization of equivariant crossed-product transitions

The algebraic transition owner does not imply continuity.  This file adds the
topological layer only through an explicit continuity witness for the
observable map, then lifts that witness coefficientwise to the finite
crossed-product carrier.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalTransitions

open CategoryTheory
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTransitions

noncomputable section

structure ContinuousEquivariantObservableMap where
  algebraMap : EquivariantObservableMap
  continuous_map : Continuous algebraMap.map

def continuousCrossedProductMap
    (Φ : ContinuousEquivariantObservableMap) :
    TopCat.of D4StarCrossedProduct ⟶ TopCat.of D4StarCrossedProduct :=
  TopCat.ofHom
    { toFun := crossedProductMap Φ.algebraMap
      continuous_toFun := by
        apply continuous_pi
        intro r
        exact Φ.continuous_map.comp (continuous_apply r) }

@[simp] theorem continuousCrossedProductMap_apply
    (Φ : ContinuousEquivariantObservableMap)
    (F : D4StarCrossedProduct) :
    continuousCrossedProductMap Φ F =
      crossedProductMap Φ.algebraMap F := rfl

theorem continuousCrossedProductMap_mul
    (Φ : ContinuousEquivariantObservableMap)
    (F K : D4StarCrossedProduct) :
    continuousCrossedProductMap Φ (crossedProductMul F K) =
      crossedProductMul
        (continuousCrossedProductMap Φ F)
        (continuousCrossedProductMap Φ K) := by
  exact crossedProductMap_mul Φ.algebraMap F K

theorem continuousCrossedProductMap_star
    (Φ : ContinuousEquivariantObservableMap)
    (F : D4StarCrossedProduct) :
    continuousCrossedProductMap Φ (crossedProductStar F) =
      crossedProductStar (continuousCrossedProductMap Φ F) := by
  exact crossedProductMap_star Φ.algebraMap F

structure ContinuousD4StarCrossedProductTransitionSystem
    (I : Type*) [Preorder I]
    extends D4StarCrossedProductTransitionSystem I where
  transition_continuous : ∀ {i j : I} (hij : i ≤ j),
    Continuous (crossedProductMap (toD4StarCrossedProductTransitionSystem.transition hij))

namespace ContinuousD4StarCrossedProductTransitionSystem

variable {I : Type*} [Preorder I]
variable (T : ContinuousD4StarCrossedProductTransitionSystem I)

def transitionTopCatHom {i j : I} (hij : i ≤ j) :
    TopCat.of D4StarCrossedProduct ⟶ TopCat.of D4StarCrossedProduct :=
  TopCat.ofHom
    { toFun := crossedProductMap (T.toD4StarCrossedProductTransitionSystem.transition hij)
      continuous_toFun := T.transition_continuous hij }

@[simp] theorem transitionTopCatHom_apply
    {i j : I} (hij : i ≤ j) (F : D4StarCrossedProduct) :
    transitionTopCatHom T hij F =
      crossedProductMap
        (T.toD4StarCrossedProductTransitionSystem.transition hij) F := rfl

theorem transitionTopCatHom_refl (i : I) :
    transitionTopCatHom T (le_refl i) = 𝟙 (TopCat.of D4StarCrossedProduct) := by
  ext F
  simp [transitionTopCatHom,
    T.toD4StarCrossedProductTransitionSystem.transition_refl]

theorem transitionTopCatHom_trans
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transitionTopCatHom T (le_trans hij hjk) =
      transitionTopCatHom T hij ≫ transitionTopCatHom T hjk := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro F
  change crossedProductMap
      (T.toD4StarCrossedProductTransitionSystem.transition (le_trans hij hjk)) F = _
  rw [T.toD4StarCrossedProductTransitionSystem.transition_trans]
  exact crossedProductMap_comp
    (T.toD4StarCrossedProductTransitionSystem.transition hjk)
    (T.toD4StarCrossedProductTransitionSystem.transition hij) F

end ContinuousD4StarCrossedProductTransitionSystem

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalTransitions
