import InfoGeometry.Canonical.MongeAmpereDualSheetBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Generic continuous real two-sheet block operators. -/

namespace InfoGeometry.Canonical.RealDoubledBlockOperator

open InfoGeometry.Krein
open InfoGeometry.Canonical.MongeAmpereDualSheetBridge

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]

noncomputable def realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (plusPointL (E := E)).comp
      (A.comp (fst_L (E := E)) + B.comp (snd_L (E := E))) +
    (minusPointL (E := E)).comp
      (C.comp (fst_L (E := E)) + D.comp (snd_L (E := E)))

omit [CompleteSpace E] in
@[simp] theorem realDoubledBlockOperator_apply
    (A B C D : E →L[ℝ] E) (x ξ : E) :
    realDoubledBlockOperator (E := E) A B C D (to_doubled x ξ) =
      to_doubled (A x + B ξ) (C x + D ξ) := by
  apply DoubledSpace.ext <;>
    simp [realDoubledBlockOperator, plusPointL, minusPointL, to_doubled,
      ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem plusBlockMap_realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) :
    plusBlockMap (E := E) (realDoubledBlockOperator A B C D) = A := by
  ext x
  simp [plusBlockMap, realDoubledBlockOperator, plusPointL, minusPointL,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem minusBlockMap_realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) :
    minusBlockMap (E := E) (realDoubledBlockOperator A B C D) = D := by
  ext x
  simp [minusBlockMap, realDoubledBlockOperator, plusPointL, minusPointL,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem plusToMinusBlockMap_realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) :
    plusToMinusBlockMap (E := E) (realDoubledBlockOperator A B C D) = C := by
  ext x
  simp [plusToMinusBlockMap, realDoubledBlockOperator, plusPointL, minusPointL,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem minusToPlusBlockMap_realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) :
    minusToPlusBlockMap (E := E) (realDoubledBlockOperator A B C D) = B := by
  ext x
  simp [minusToPlusBlockMap, realDoubledBlockOperator, plusPointL, minusPointL,
    ContinuousLinearMap.comp_apply]

end
end InfoGeometry.Canonical.RealDoubledBlockOperator
