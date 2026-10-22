/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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
    simp [realDoubledBlockOperator, to_doubled,
      ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem plusBlockMap_realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) :
    plusBlockMap (E := E) (realDoubledBlockOperator A B C D) = A := by
  ext x
  simp [plusBlockMap, realDoubledBlockOperator,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem minusBlockMap_realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) :
    minusBlockMap (E := E) (realDoubledBlockOperator A B C D) = D := by
  ext x
  simp [minusBlockMap, realDoubledBlockOperator,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem plusToMinusBlockMap_realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) :
    plusToMinusBlockMap (E := E) (realDoubledBlockOperator A B C D) = C := by
  ext x
  simp [plusToMinusBlockMap, realDoubledBlockOperator,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem minusToPlusBlockMap_realDoubledBlockOperator
    (A B C D : E →L[ℝ] E) :
    minusToPlusBlockMap (E := E) (realDoubledBlockOperator A B C D) = B := by
  ext x
  simp [minusToPlusBlockMap, realDoubledBlockOperator,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
theorem realDoubledBlockOperator_comp
    (A B C D A' B' C' D' : E →L[ℝ] E) :
    (realDoubledBlockOperator A B C D).comp
        (realDoubledBlockOperator A' B' C' D') =
      realDoubledBlockOperator
        (A.comp A' + B.comp C') (A.comp B' + B.comp D')
        (C.comp A' + D.comp C') (C.comp B' + D.comp D') := by
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨x, ξ⟩ := z
  simp only [ContinuousLinearMap.comp_apply,
    realDoubledBlockOperator_apply]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    map_add]
  apply congrArg₂ to_doubled <;> abel

omit [CompleteSpace E] in
@[simp] theorem realDoubledBlockOperator_identity :
    realDoubledBlockOperator
        (1 : E →L[ℝ] E) 0 0 (1 : E →L[ℝ] E) =
      (1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨x, ξ⟩ := z
  simp only [realDoubledBlockOperator_apply, zero_apply,
    add_zero, zero_add]
  rfl

end
end InfoGeometry.Canonical.RealDoubledBlockOperator
