/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.RealDoubledOperatorAdjointTransport
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# Compactness under the real doubled-carrier transport

This owner supplies the compactness lemma needed by a later transport of
bounded real split-Krein cycle defects.  The proof uses the actual continuous
linear equivalence between `DoubledSpace E` and `HilbertDoubled E`; it does not
replace compactness by a proposition field or by finite-dimensionality.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem isCompactOperator_conjugateDoubledEnd
    (T : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hT : IsCompactOperator (T : DoubledSpace E → DoubledSpace E)) :
    IsCompactOperator
      (conjugateDoubledEnd (E := E) T :
        HilbertDoubled E → HilbertDoubled E) := by
  have h_inner :
      IsCompactOperator
        ((T.comp
          (HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap :
          HilbertDoubled E →L[ℝ] DoubledSpace E) :
          HilbertDoubled E → DoubledSpace E) := by
    simpa [ContinuousLinearMap.coe_comp] using
      (IsCompactOperator.comp_clm (hf := hT)
        (g := (HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap))
  simpa [conjugateDoubledEnd, ContinuousLinearMap.coe_comp] using
    (IsCompactOperator.clm_comp (hf := h_inner)
      (g := (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap))

theorem isCompactOperator_of_conjugateDoubledEnd
    (T : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hT : IsCompactOperator
      (conjugateDoubledEnd (E := E) T : HilbertDoubled E → HilbertDoubled E)) :
    IsCompactOperator (T : DoubledSpace E → DoubledSpace E) := by
  have h_inner : IsCompactOperator
      ((conjugateDoubledEnd (E := E) T).comp
        (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap :
        DoubledSpace E → HilbertDoubled E) := by
    simpa [ContinuousLinearMap.coe_comp] using
      (IsCompactOperator.comp_clm (hf := hT)
        (g := (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap))
  have h_outer : IsCompactOperator
      ((HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap.comp
        ((conjugateDoubledEnd (E := E) T).comp
          (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap) :
        DoubledSpace E → DoubledSpace E) := by
    simpa [ContinuousLinearMap.coe_comp] using
      (IsCompactOperator.clm_comp (hf := h_inner)
        (g := (HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap))
  have h_eq :
      (HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap.comp
        ((conjugateDoubledEnd (E := E) T).comp
          (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap) = T := by
    apply ContinuousLinearMap.ext
    intro x
    simp [conjugateDoubledEnd, ContinuousLinearMap.comp_apply]
  rw [h_eq] at h_outer
  exact h_outer

end InfoGeometry.Krein
