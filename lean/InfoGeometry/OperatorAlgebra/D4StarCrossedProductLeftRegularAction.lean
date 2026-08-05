import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

/-!
# Left-regular action on the finite D₄ crossed-product carrier

Left multiplication gives an honest noncommutative operator action.  Since
the finite carrier is not yet equipped with a proved topological algebra
structure, continuity is carried by an explicit witness rather than inferred
or postulated.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductLeftRegularAction

open CategoryTheory
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

noncomputable section

def leftRegularAction (F : D4StarCrossedProduct) :
    D4StarCrossedProduct → D4StarCrossedProduct :=
  fun K => crossedProductMul F K

@[simp] theorem leftRegularAction_apply
    (F K : D4StarCrossedProduct) :
    leftRegularAction F K = crossedProductMul F K := rfl

theorem leftRegularAction_comp
    (F K : D4StarCrossedProduct) :
    leftRegularAction (crossedProductMul F K) =
      leftRegularAction F ∘ leftRegularAction K := by
  funext L
  exact crossedProductMul_assoc F K L

structure ContinuousLeftRegularAction where
  continuous_left : ∀ F : D4StarCrossedProduct,
    Continuous (leftRegularAction F)

variable (W : ContinuousLeftRegularAction)

def leftRegularActionTopCatHom (F : D4StarCrossedProduct) :
    TopCat.of D4StarCrossedProduct ⟶ TopCat.of D4StarCrossedProduct :=
  TopCat.ofHom
    { toFun := leftRegularAction F
      continuous_toFun := W.continuous_left F }

@[simp] theorem leftRegularActionTopCatHom_apply
    (F K : D4StarCrossedProduct) :
    leftRegularActionTopCatHom W F K = crossedProductMul F K := rfl

  theorem leftRegularActionTopCatHom_comp
    (F K : D4StarCrossedProduct) :
    leftRegularActionTopCatHom W (crossedProductMul F K) =
      leftRegularActionTopCatHom W K ≫ leftRegularActionTopCatHom W F := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro L
  exact crossedProductMul_assoc F K L

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductLeftRegularAction
