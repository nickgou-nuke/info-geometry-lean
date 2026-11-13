/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# A compact phase with compact square defect forces finite dimension

This is an obstruction for proposed bounded transforms, not a replacement
definition of a Fredholm phase. It applies to arbitrary real normed spaces.
-/

namespace InfoGeometry.KK.CompactPhaseObstruction

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- If `F` and `F² - 1` are compact, their difference exhibits compact identity. -/
theorem finiteDimensional_of_compact_phase
    (F : H →L[ℝ] H) (hF : IsCompactOperator F)
    (hDefect : IsCompactOperator (F * F - 1 : H →L[ℝ] H)) :
    FiniteDimensional ℝ H := by
  have hSquare : IsCompactOperator (F * F : H →L[ℝ] H) := hF.clm_comp F
  have hId : IsCompactOperator (id : H → H) := by
    convert hSquare.sub hDefect using 1
    ext x
    simp
  exact FiniteDimensional.of_isCompactOperator_id hId

/-- A bounded operator with a compact bounded left inverse also forces finite dimension. -/
theorem finiteDimensional_of_compact_left_inverse
    (A R : H →L[ℝ] H) (hR : IsCompactOperator R)
    (hInverse : R.comp A = ContinuousLinearMap.id ℝ H) :
    FiniteDimensional ℝ H := by
  have hCompact : IsCompactOperator (R.comp A) := hR.comp_clm A
  rw [hInverse] at hCompact
  exact FiniteDimensional.of_isCompactOperator_id hCompact

end InfoGeometry.KK.CompactPhaseObstruction
