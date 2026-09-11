import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bundled coefficientwise comparison for crossed-product descent

This packet packages the concrete comparison laws already proved for the
finite-stage crossed-product carrier and the coefficient-limit convolution.
It deliberately does not install a global algebra instance on the function
carrier and does not assert a universal crossed-product/direct-limit
isomorphism.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonPacket

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution

noncomputable section

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarGroupAction I G Stage sys)

/-- The coefficientwise comparison map, viewed as a family in the stage index. -/
def coefficientwiseComparisonFamily :
    ∀ i : I, stageCrossedProduct I G Stage i → (G → limitCoefficient Stage sys) :=
  fun i => coefficientwiseComparison I G Stage sys i

theorem coefficientwiseComparisonFamily_transition
    {i j : I} (hij : i ≤ j)
    (F : stageCrossedProduct I G Stage i) :
    coefficientwiseComparisonFamily Stage sys i F =
      coefficientwiseComparisonFamily Stage sys j (fun g => sys.map hij (F g)) := by
  funext g
  simpa [coefficientwiseComparisonFamily, coefficientwiseComparison] using
    (algebraicStarDirectLimitOf_transition Stage sys hij (F g)).symm

@[simp] theorem coefficientwiseComparisonPacket_apply
    (i : I) (F : stageCrossedProduct I G Stage i) (g : G) :
    coefficientwiseComparison I G Stage sys i F g =
      algebraicStarDirectLimitOf Stage sys i (F g) :=
  coefficientwiseComparison_apply (I := I) (G := G) (Stage := Stage) (sys := sys) i F g

theorem coefficientwiseComparisonPacket_zero
    (i : I) :
    coefficientwiseComparison I G Stage sys i
        (0 : stageCrossedProduct I G Stage i) = 0 := by
  funext g
  simpa [coefficientwiseComparison] using
    (map_zero (algebraicStarDirectLimitOf Stage sys i) :
      algebraicStarDirectLimitOf Stage sys i (0 : Stage i) = 0)

theorem coefficientwiseComparisonPacket_add
    (i : I)
    (F K : stageCrossedProduct I G Stage i) :
    coefficientwiseComparison I G Stage sys i (F + K) =
      coefficientwiseComparison I G Stage sys i F +
        coefficientwiseComparison I G Stage sys i K := by
  funext g
  exact (algebraicStarDirectLimitOf Stage sys i).map_add (F g) (K g)

theorem coefficientwiseComparisonPacket_convolution
    (i : I) (F K : stageCrossedProduct I G Stage i) :
    coefficientwiseComparison I G Stage sys i
        (stageConvolution I G Stage sys A i F K) =
      limitConvolution I G Stage sys A
        (coefficientwiseComparison I G Stage sys i F)
        (coefficientwiseComparison I G Stage sys i K) := by
  simpa [coefficientwiseComparison, stageConvolution, limitConvolution]
    using
      InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution.coefficientwiseComparison_convolution
        (Stage := Stage) (sys := sys) (A := A) i F K

theorem coefficientwiseComparisonPacket_star
    (i : I) (F : stageCrossedProduct I G Stage i) :
    coefficientwiseComparison I G Stage sys i
        (stageConvolutionStar I G Stage sys A i F) =
      limitConvolutionStar I G Stage sys A
        (coefficientwiseComparison I G Stage sys i F) := by
  simpa [coefficientwiseComparison, stageConvolutionStar, limitConvolutionStar]
    using
        InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution.coefficientwiseComparison_star
        (Stage := Stage) (sys := sys) (A := A) i F

theorem coefficientwiseComparisonPacket_one
    (i : I) :
    coefficientwiseComparison I G Stage sys i
        (fun g => if g = 1 then 1 else 0) =
      limitConvolutionOne I G Stage sys := by
  funext g
  by_cases h : g = 1
  · subst h
    simp [coefficientwiseComparison, limitConvolutionOne]
    rw [DirectLimit.one_def]
  · simp [coefficientwiseComparison, limitConvolutionOne, h]
    exact (algebraicStarDirectLimitOf Stage sys i).map_zero

end

end InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonPacket
