/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.RealDoubledCompactTransport

/-!
# Compact defect transport on the real doubled carrier

These lemmas are the operator-level boundary needed before transporting a
real split-Krein cycle.  They transport the actual square and commutator
defects, rather than asserting a cycle-level equivalence without its compact
operator obligations.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem isCompactOperator_conjugateDoubledEnd_square_defect
    (T : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hT : IsCompactOperator
      ((T.comp T - (ContinuousLinearMap.id ℝ (DoubledSpace E)) :
        DoubledSpace E →L[ℝ] DoubledSpace E) :
        DoubledSpace E → DoubledSpace E)) :
    IsCompactOperator
      (((conjugateDoubledEnd (E := E) T).comp
          (conjugateDoubledEnd (E := E) T) -
          (ContinuousLinearMap.id ℝ (HilbertDoubled E)) :
        HilbertDoubled E →L[ℝ] HilbertDoubled E) :
        HilbertDoubled E → HilbertDoubled E) := by
  have htransport :
      (conjugateDoubledEnd (E := E) T).comp
          (conjugateDoubledEnd (E := E) T) -
          (ContinuousLinearMap.id ℝ (HilbertDoubled E)) =
        conjugateDoubledEnd (E := E)
          (T.comp T - (ContinuousLinearMap.id ℝ (DoubledSpace E))) := by
    apply ContinuousLinearMap.ext
    intro x
    simp [conjugateDoubledEnd, ContinuousLinearMap.comp_apply]
  rw [htransport]
  exact isCompactOperator_conjugateDoubledEnd _ hT

theorem isCompactOperator_conjugateDoubledEnd_commutator
    (S T : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hST : IsCompactOperator
      ((S.comp T - T.comp S : DoubledSpace E →L[ℝ] DoubledSpace E) :
        DoubledSpace E → DoubledSpace E)) :
    IsCompactOperator
      (((conjugateDoubledEnd (E := E) S).comp
          (conjugateDoubledEnd (E := E) T) -
          (conjugateDoubledEnd (E := E) T).comp
            (conjugateDoubledEnd (E := E) S) :
        HilbertDoubled E →L[ℝ] HilbertDoubled E) :
        HilbertDoubled E → HilbertDoubled E) := by
  have htransport :
      (conjugateDoubledEnd (E := E) S).comp
          (conjugateDoubledEnd (E := E) T) -
          (conjugateDoubledEnd (E := E) T).comp
            (conjugateDoubledEnd (E := E) S) =
        conjugateDoubledEnd (E := E) (S.comp T - T.comp S) := by
    apply ContinuousLinearMap.ext
    intro x
    simp [conjugateDoubledEnd, ContinuousLinearMap.comp_apply]
  rw [htransport]
  exact isCompactOperator_conjugateDoubledEnd _ hST

end InfoGeometry.Krein
