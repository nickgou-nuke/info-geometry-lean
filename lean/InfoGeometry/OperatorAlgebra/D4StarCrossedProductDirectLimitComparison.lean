import InfoGeometry.Canonical.D4StarObservableDirectLimitAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PauliJungTrialityD4Synthesis
import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution
import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTopologicalFamily

/-!
# D₄-star coefficientwise crossed-product comparison

This file specializes the coefficientwise comparison pattern to the D₄
crossed-product carrier over the constant observable system.

It keeps the crossed-product carrier explicitly noncommutative, but it only
records the coefficientwise descent into the native filtered star direct limit.
No crossed-product completion or colimit theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductDirectLimitComparison

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open InfoGeometry.Canonical.D4StarObservableDirectLimitAction
open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTopologicalFamily

/-- The native direct limit of the constant observable system. -/
abbrev D4ObservableDirectLimit :=
  AlgebraicStarDirectLimit ObservableStage constantObservableSystem

/-- The coefficientwise comparison map into the native star direct limit. -/
def coefficientwiseComparison (i : ℕ) :
    crossedProduct (Equiv.Perm ColorChannel) ObservableStage i →
      (Equiv.Perm ColorChannel → D4ObservableDirectLimit) :=
  fun F g =>
      algebraicStarDirectLimitOf ObservableStage
        constantObservableSystem i (F g)

@[simp] theorem coefficientwiseComparison_apply
    (i : ℕ) (F : crossedProduct (Equiv.Perm ColorChannel) ObservableStage i)
    (g : Equiv.Perm ColorChannel) :
    coefficientwiseComparison i F g =
      algebraicStarDirectLimitOf ObservableStage
        constantObservableSystem i (F g) :=
  rfl

theorem coefficientwiseComparison_transition
    {i j : ℕ} (hij : i ≤ j)
    (F : crossedProduct (Equiv.Perm ColorChannel) ObservableStage i) :
    coefficientwiseComparison j (fun g => constantObservableSystem.map hij (F g)) =
      coefficientwiseComparison i F := by
  funext g
  simpa [coefficientwiseComparison] using
    algebraicStarDirectLimitOf_transition
      ObservableStage constantObservableSystem hij (F g)

theorem coefficientwiseComparison_zero
    (i : ℕ) :
    coefficientwiseComparison i (0 : crossedProduct (Equiv.Perm ColorChannel) ObservableStage i) =
      0 := by
  funext g
  simpa [coefficientwiseComparison] using
    (map_zero (algebraicStarDirectLimitOf ObservableStage
      constantObservableSystem i) : algebraicStarDirectLimitOf ObservableStage
      constantObservableSystem i (0 : ObservableStage i) = 0)

theorem coefficientwiseComparison_add
    (i : ℕ)
    (F K : crossedProduct (Equiv.Perm ColorChannel) ObservableStage i) :
    coefficientwiseComparison i (F + K) =
      coefficientwiseComparison i F + coefficientwiseComparison i K := by
  funext g
  exact (algebraicStarDirectLimitOf ObservableStage
    constantObservableSystem i).map_add (F g) (K g)

theorem coefficientwiseComparison_convolution
    (i : ℕ)
    (F K : crossedProduct (Equiv.Perm ColorChannel) ObservableStage i) :
    coefficientwiseComparison i (crossedProductMul F K) =
      limitConvolution ℕ (Equiv.Perm ColorChannel) ObservableStage
        constantObservableSystem observableAction
        (coefficientwiseComparison i F)
        (coefficientwiseComparison i K) := by
  simpa [coefficientwiseComparison, crossedProductMul, limitConvolution,
    ObservableStage, constantObservableSystem, observableAction,
    InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution.stageConvolution] using
    InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution.coefficientwiseComparison_convolution
      (Stage := ObservableStage) (sys := constantObservableSystem)
      (A := observableAction) i F K

theorem coefficientwiseComparison_star
    (i : ℕ)
    (F : crossedProduct (Equiv.Perm ColorChannel) ObservableStage i) :
    coefficientwiseComparison i (crossedProductStar F) =
      limitConvolutionStar ℕ (Equiv.Perm ColorChannel) ObservableStage
        constantObservableSystem observableAction
        (coefficientwiseComparison i F) := by
  simpa [coefficientwiseComparison, crossedProductStar, limitConvolutionStar,
    ObservableStage, constantObservableSystem, observableAction,
    InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution.stageConvolutionStar] using
    InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution.coefficientwiseComparison_star
      (Stage := ObservableStage) (sys := constantObservableSystem)
      (A := observableAction) i F

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductDirectLimitComparison
