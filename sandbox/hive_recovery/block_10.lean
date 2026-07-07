import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace InfoGeometry.Canonical

/--
Continuous linear map adjoint difference preservation.
-/
theorem adjoint_sub_eq_sub_adjoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u v : E →L[ℝ] E) :
    ContinuousLinearMap.adjoint (u - v) = ContinuousLinearMap.adjoint u - ContinuousLinearMap.adjoint v := by
  ext x y
  simp

/-
BUCKET 1: CLOSED FINITE THEOREMS
- InfoGeometry.Canonical.adjoint_sub_eq_sub_adjoint

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- None

BUCKET 3: OPEN CLOSURE DEBT
- None
-/

end InfoGeometry.Canonical