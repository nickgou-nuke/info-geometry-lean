import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace InfoGeometry.Canonical

/--
Continuous linear map adjoint conjugate involution preservation.
-/
theorem adjoint_adjoint_eq_self {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : E →L[ℝ] E) :
    ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint u) = u := by
  ext x y
  simp

/-
BUCKET 1: CLOSED FINITE THEOREMS
- InfoGeometry.Canonical.adjoint_adjoint_eq_self

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- None

BUCKET 3: OPEN CLOSURE DEBT
- None
-/

end InfoGeometry.Canonical