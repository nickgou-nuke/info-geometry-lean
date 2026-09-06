import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Split-octonion norm composition

This module closes the symbolic norm-composition check from
`tools/sympy/split_octonion_multiplication.py` inside Lean.

The result is purely algebraic over the explicit integer Zorn multiplication
surface: `detZ (mulZ X Y) = detZ X * detZ Y`.

It does not assert a `G₂(2)` automorphism theorem, an `SU(3)` stabilizer theorem,
or any particle-classification theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.NormComposition

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- The Zorn split norm composes multiplicatively under the explicit product. -/
theorem detZ_mulZ (X Y : SplitOct) : detZ (mulZ X Y) = detZ X * detZ Y := by
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      unfold detZ mulZ
      ring

/-- The diagonal idempotents are split-null for the composing norm. -/
theorem diagonal_idempotents_split_null : detZ ePlus = 0 ∧ detZ eMinus = 0 := by
  constructor <;> rfl

end InfoGeometry.OperatorAlgebra.SplitOctonions.NormComposition
