import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTopologicalFamily
import InfoGeometry.Canonical.FilteredStarAlgebraActionDirectLimit

/-!
# Coefficientwise comparison with the native star direct limit

The crossed-product carrier is not yet equipped with a C*-algebra structure,
so this file does not claim a crossed-product direct limit.  It records the
honest comparison map obtained by applying the native coefficient injection at
each group coordinate.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitComparison

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTopologicalFamily

noncomputable section

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

abbrev CoefficientDirectLimit :=
  AlgebraicStarDirectLimit Stage sys

def coefficientwiseComparison (i : I) :
    crossedProduct G Stage i → (G → CoefficientDirectLimit Stage sys) :=
  fun F g => algebraicStarDirectLimitOf Stage sys i (F g)

@[simp] theorem coefficientwiseComparison_apply
    (i : I) (F : crossedProduct G Stage i) (g : G) :
    coefficientwiseComparison Stage sys i F g =
      algebraicStarDirectLimitOf Stage sys i (F g) := rfl

theorem coefficientwiseComparison_transition
    {i j : I} (hij : i ≤ j) (F : crossedProduct G Stage i) :
    coefficientwiseComparison Stage sys j
        (fun g => sys.map hij (F g)) =
      coefficientwiseComparison Stage sys i F := by
  funext g
  exact algebraicStarDirectLimitOf_transition Stage sys hij (F g)

theorem coefficientwiseComparison_zero
    (i : I) :
    coefficientwiseComparison Stage sys i (0 : crossedProduct G Stage i) = 0 := by
  funext g
  change algebraicStarDirectLimitOf Stage sys i (0 : Stage i) = 0
  exact map_zero _

theorem coefficientwiseComparison_add
    (i : I) (F K : crossedProduct G Stage i) :
    coefficientwiseComparison Stage sys i (F + K) =
      coefficientwiseComparison Stage sys i F +
        coefficientwiseComparison Stage sys i K := by
  funext g
  change algebraicStarDirectLimitOf Stage sys i (F g + K g) =
    algebraicStarDirectLimitOf Stage sys i (F g) +
      algebraicStarDirectLimitOf Stage sys i (K g)
  exact map_add _ _ _

end

end InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitComparison
