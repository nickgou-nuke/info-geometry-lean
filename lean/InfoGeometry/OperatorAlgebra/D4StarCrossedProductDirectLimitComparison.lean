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
  funext r
  rw [coefficientwiseComparison_apply]
  change (algebraicStarDirectLimitOf ObservableStage constantObservableSystem i)
      (∑ g : Equiv.Perm ColorChannel,
        D4StarCrossedProduct.coeff F g *
        colorPullback g (D4StarCrossedProduct.coeff K (g.symm * r))) = _
  rw [map_sum]
  rw [limitConvolution]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_mul]
  rw [coefficientwiseComparison_apply, coefficientwiseComparison_apply]
  change (algebraicStarDirectLimitOf ObservableStage constantObservableSystem i) (D4StarCrossedProduct.coeff F g) *
      (algebraicStarDirectLimitOf ObservableStage constantObservableSystem i)
        (colorPullback g (D4StarCrossedProduct.coeff K (g.symm * r))) =
    (algebraicStarDirectLimitOf ObservableStage constantObservableSystem i) (F g) *
      observableColimitAction g
        ((algebraicStarDirectLimitOf ObservableStage constantObservableSystem i) (K (g⁻¹ * r)))
  rw [observableColimitAction_on_stage]
  rfl

theorem coefficientwiseComparison_star
    (i : ℕ)
    (F : crossedProduct (Equiv.Perm ColorChannel) ObservableStage i) :
    coefficientwiseComparison i (crossedProductStar F) =
      limitConvolutionStar ℕ (Equiv.Perm ColorChannel) ObservableStage
        constantObservableSystem observableAction
        (coefficientwiseComparison i F) := by
  funext r
  rw [coefficientwiseComparison_apply]
  rw [limitConvolutionStar]
  rw [coefficientwiseComparison_apply]
  change (algebraicStarDirectLimitOf ObservableStage constantObservableSystem i)
      (crossedProductStar F r) =
    observableColimitAction r
      (star ((algebraicStarDirectLimitOf ObservableStage constantObservableSystem i) (F r⁻¹)))
  rw [← map_star (algebraicStarDirectLimitOf ObservableStage constantObservableSystem i)]
  rw [observableColimitAction_on_stage]
  rfl

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductDirectLimitComparison
