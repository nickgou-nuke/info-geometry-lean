import InfoGeometry.Categorical.FibonacciPentagonPathCarrier
import InfoGeometry.Categorical.FibonacciFusionTreeAssociator

/-!
# Genuine local associators on the four-`τ` pentagon

These are the pentagon edges that are honest whiskerings of the already
proved three-`τ` Fibonacci associator.  The remaining edges involve a
composite object as one input and require a separate composite-channel
associator; they are intentionally not manufactured here.
-/

namespace InfoGeometry.Categorical.FibonacciFourAnyonLocalAssociators

open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionTreeAssociator
open InfoGeometry.Categorical.FibonacciPentagonPathCarrier

noncomputable def localEdgeOne (τ s : ℂ) :
    FibHom (parenthesizedObject .vertex₁)
      (parenthesizedObject .vertex₃) := by
  simpa [parenthesizedObject, fourTau, tauObject] using
    (fibWhiskerRight (tauFusionTreeAssociator τ s) tauObject)

noncomputable def localEdgeThree (τ s : ℂ) :
    FibHom (parenthesizedObject .vertex₄)
      (parenthesizedObject .vertex₅) := by
  simpa [parenthesizedObject, fourTau, tauObject] using
    (fibWhiskerLeft tauObject (tauFusionTreeAssociator τ s))

theorem localEdgeOne_is_whiskered (τ s : ℂ) :
    localEdgeOne τ s =
      (by
        simpa [parenthesizedObject, fourTau, tauObject] using
          (fibWhiskerRight (tauFusionTreeAssociator τ s) tauObject)) := by
  rfl

theorem localEdgeThree_is_whiskered (τ s : ℂ) :
    localEdgeThree τ s =
      (by
        simpa [parenthesizedObject, fourTau, tauObject] using
          (fibWhiskerLeft tauObject (tauFusionTreeAssociator τ s))) := by
  rfl

theorem localEdgeOne_comp_inverse
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (localEdgeOne τ s)
      (by
        simpa [parenthesizedObject, fourTau, tauObject] using
          (fibWhiskerRight (tauFusionTreeAssociatorInv τ s) tauObject)) =
      FibHom.id (parenthesizedObject .vertex₁) := by
  change FibHom.comp
      (fibWhiskerRight (tauFusionTreeAssociator τ s) tauObject)
      (fibWhiskerRight (tauFusionTreeAssociatorInv τ s) tauObject) = _
  simp only [fibWhiskerRight]
  rw [← fibTensorHom_comp]
  rw [tauFusionTreeAssociator_comp_inv τ s hs hτ]
  simpa [FibHom.comp, FibHom.id, parenthesizedObject, fourTau, tauObject] using
    (fibTensorHom_id
      (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      tauObject)

theorem localEdgeThree_comp_inverse
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (localEdgeThree τ s)
      (by
        simpa [parenthesizedObject, fourTau, tauObject] using
          (fibWhiskerLeft tauObject (tauFusionTreeAssociatorInv τ s))) =
      FibHom.id (parenthesizedObject .vertex₄) := by
  change FibHom.comp
      (fibWhiskerLeft tauObject (tauFusionTreeAssociator τ s))
      (fibWhiskerLeft tauObject (tauFusionTreeAssociatorInv τ s)) = _
  simp only [fibWhiskerLeft]
  rw [← fibTensorHom_comp]
  rw [tauFusionTreeAssociator_comp_inv τ s hs hτ]
  simpa [FibHom.comp, FibHom.id, parenthesizedObject, fourTau, tauObject] using
    (fibTensorHom_id tauObject
      (fibTensorObj (fibTensorObj tauObject tauObject) tauObject))

end InfoGeometry.Categorical.FibonacciFourAnyonLocalAssociators
