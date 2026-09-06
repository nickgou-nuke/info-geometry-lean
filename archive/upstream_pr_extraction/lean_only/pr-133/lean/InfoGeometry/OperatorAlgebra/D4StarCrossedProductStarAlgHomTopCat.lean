import InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarAlgHomContinuity
import InfoGeometry.OperatorAlgebra.D4StarCrossedProductTransitions

/-!
# TopCat packaging of the finite equivariant crossed-product action

The coefficientwise `StarAlgHom` is already algebraically multiplicative and
star preserving.  Finite-dimensional continuity lets us package the same map
as a `TopCat` morphism, while keeping the algebraic and topological carriers
distinct.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarAlgHomTopCat

open CategoryTheory
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarAlgHomContinuity
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTransitions

noncomputable section

def crossedProductStarAlgHomTopCat
    (Φ : EquivariantObservableMap) :
    TopCat.of D4StarCrossedProduct ⟶ TopCat.of D4StarCrossedProduct :=
  TopCat.ofHom
    { toFun := crossedProductMap Φ
      continuous_toFun := continuous_crossedProductMap Φ }

@[simp] theorem crossedProductStarAlgHomTopCat_apply
    (Φ : EquivariantObservableMap) (F : D4StarCrossedProduct) :
    crossedProductStarAlgHomTopCat Φ F = crossedProductMap Φ F :=
  rfl

theorem crossedProductStarAlgHomTopCat_mul
    (Φ : EquivariantObservableMap)
    (F K : D4StarCrossedProduct) :
    crossedProductStarAlgHomTopCat Φ (crossedProductMul F K) =
      crossedProductMul
        (crossedProductStarAlgHomTopCat Φ F)
        (crossedProductStarAlgHomTopCat Φ K) := by
  exact crossedProductMap_mul Φ F K

@[simp] theorem crossedProductStarAlgHomTopCat_identity :
    crossedProductStarAlgHomTopCat identityObservableMap =
      𝟙 (TopCat.of D4StarCrossedProduct) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro F
  change crossedProductMap identityObservableMap F = F
  exact crossedProductMap_identity F

theorem crossedProductStarAlgHomTopCat_comp
    (Φ Ψ : EquivariantObservableMap) :
    crossedProductStarAlgHomTopCat (observableMapComp Ψ Φ) =
      crossedProductStarAlgHomTopCat Φ ≫
        crossedProductStarAlgHomTopCat Ψ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro F
  change crossedProductMap (observableMapComp Ψ Φ) F =
    crossedProductMap Ψ (crossedProductMap Φ F)
  exact crossedProductMap_comp Ψ Φ F

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarAlgHomTopCat
