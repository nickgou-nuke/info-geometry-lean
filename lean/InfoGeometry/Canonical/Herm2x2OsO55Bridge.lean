import InfoGeometry.Algebra.JordanCayleyInversionOs
import InfoGeometry.Physics.Pin55Formal
import Mathlib.Tactic

/-!
# Concrete `J₂(𝕆_s)` to `q₅₅` coordinate bridge

The live `Herm2x2Os` carrier has rational light-cone coordinates and an integer
`SplitOct` Zorn cell.  Consequently this file proves the forward rational
coordinate readout and its determinant identity, but does not claim a rational
linear equivalence until an explicit rational base-change carrier is introduced.
-/

open InfoGeometry.Algebra.JordanCayleyInversionOs
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace InfoGeometry.Canonical.Herm2x2OsO55Bridge

/-- The rational coordinates of `J₂(𝕆_s)` in the diagonal `(5,5)` convention. -/
def toVec55 (X : Herm2x2Os) : Fin 10 → ℚ :=
  ![(X.xp + X.xm) / 2,
    ((X.z.a : ℚ) - X.z.b) / 2,
    ((X.z.x0 : ℚ) + X.z.y0) / 2,
    ((X.z.x1 : ℚ) + X.z.y1) / 2,
    ((X.z.x2 : ℚ) + X.z.y2) / 2,
    (X.xp - X.xm) / 2,
    ((X.z.a : ℚ) + X.z.b) / 2,
    ((X.z.x0 : ℚ) - X.z.y0) / 2,
    ((X.z.x1 : ℚ) - X.z.y1) / 2,
    ((X.z.x2 : ℚ) - X.z.y2) / 2]

/-- The Zorn determinant is exactly the canonical split `(5,5)` quadratic form. -/
theorem det_eq_q55_toVec55 (X : Herm2x2Os) :
    X.det = InfoGeometry.Physics.Pin55Formal.q55 (toVec55 X) := by
  unfold Herm2x2Os.det toVec55 InfoGeometry.Physics.Pin55Formal.q55
  simp [QuadraticMap.proj, zornNormℚ]
  ring

/-- The same compatibility with the orientation used by the quadratic-form API. -/
theorem q55_toVec55_eq_det (X : Herm2x2Os) :
    InfoGeometry.Physics.Pin55Formal.q55 (toVec55 X) = X.det :=
  (det_eq_q55_toVec55 X).symm

end InfoGeometry.Canonical.Herm2x2OsO55Bridge
