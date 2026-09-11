import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Odd-sector associator readout for the split-octonion Zorn carrier

This is the native algebraic part of the proposed spacetime associator bridge.
It deliberately stops at the concrete `SplitOct` carrier: differential forms
and Penrose contour integration belong to separate geometric layers.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

def oddZ (x0 x1 x2 y0 y1 y2 : ℤ) : SplitOct :=
  ⟨0, 0, x0, x1, x2, y0, y1, y2⟩

def det3 (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℤ) : ℤ :=
  a0 * (b1 * c2 - b2 * c1) -
    a1 * (b0 * c2 - b2 * c0) +
    a2 * (b0 * c1 - b1 * c0)

/-- The associator of three purely off-diagonal Zorn elements is diagonal.
Its two diagonal entries are opposite scalar triple products of the upper and
lower vectors. -/
theorem odd_associator_diagonal_formula
    (x0 x1 x2 y0 y1 y2 : ℤ)
    (u0 u1 u2 v0 v1 v2 : ℤ)
    (r0 r1 r2 s0 s1 s2 : ℤ) :
    (associator (oddZ x0 x1 x2 y0 y1 y2)
      (oddZ u0 u1 u2 v0 v1 v2)
      (oddZ r0 r1 r2 s0 s1 s2)).a =
        - det3 y0 y1 y2 v0 v1 v2 s0 s1 s2 -
          det3 x0 x1 x2 u0 u1 u2 r0 r1 r2 ∧
    (associator (oddZ x0 x1 x2 y0 y1 y2)
      (oddZ u0 u1 u2 v0 v1 v2)
      (oddZ r0 r1 r2 s0 s1 s2)).b =
        det3 x0 x1 x2 u0 u1 u2 r0 r1 r2 +
          det3 y0 y1 y2 v0 v1 v2 s0 s1 s2 := by
  constructor <;> simp [associator, oddZ, det3, mulZ, subZ] <;> ring

/-
theorem odd_associator_off_diagonal_zero
    (x0 x1 x2 y0 y1 y2 u0 u1 u2 v0 v1 v2 r0 r1 r2 s0 s1 s2 : ℤ) :
    (associator (oddZ x0 x1 x2 y0 y1 y2)
      (oddZ u0 u1 u2 v0 v1 v2)
      (oddZ r0 r1 r2 s0 s1 s2)).x0 = 0 ∧
    (associator (oddZ x0 x1 x2 y0 y1 y2)
      (oddZ u0 u1 u2 v0 v1 v2)
      (oddZ r0 r1 r2 s0 s1 s2)).x1 = 0 ∧
    (associator (oddZ x0 x1 x2 y0 y1 y2)
      (oddZ u0 u1 u2 v0 v1 v2)
      (oddZ r0 r1 r2 s0 s1 s2)).x2 = 0 ∧
    (associator (oddZ x0 x1 x2 y0 y1 y2)
      (oddZ u0 u1 u2 v0 v1 v2)
      (oddZ r0 r1 r2 s0 s1 s2)).y0 = 0 ∧
    (associator (oddZ x0 x1 x2 y0 y1 y2)
      (oddZ u0 u1 u2 v0 v1 v2)
      (oddZ r0 r1 r2 s0 s1 s2)).y1 = 0 ∧
    (associator (oddZ x0 x1 x2 y0 y1 y2)
      (oddZ u0 u1 u2 v0 v1 v2)
      (oddZ r0 r1 r2 s0 s1 s2)).y2 = 0 := by
  have h := odd_associator_diagonal_formula
    x0 x1 x2 y0 y1 y2 u0 u1 u2 v0 v1 v2 r0 r1 r2 s0 s1 s2
  simp only [h]
-/

end InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
