import InfoGeometry.Algebra.JordanCayleyInversionOs
import InfoGeometry.Algebra.SplitOctonionIsomorphism
import InfoGeometry.Physics.Pin55Formal
import InfoGeometry.Canonical.Herm2x2OsO55RationalBridge
import Mathlib.Tactic

/-!
# Concrete `J₂(𝕆_s)` to `q₅₅` coordinate bridge

The live `Herm2x2Os` carrier has rational light-cone coordinates and an integer
`SplitOct` Zorn cell.  The rational base-change carrier is provided by
`hermitianPromotion` and `Herm2x2OsO55RationalBridge`; this file records the
compatibility of the mixed-carrier readout with that existing rational owner.
-/

open InfoGeometry.Algebra.JordanCayleyInversionOs
open InfoGeometry.Algebra.SplitOctonionIsomorphism
open InfoGeometry.Physics.Pin55Formal
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

/-- The mixed-carrier coordinates are the rational coordinates after promotion.

This is the commuting square between the integral Zorn/Jordan carrier and the
already-defined pure-rational `(5,5)` carrier. -/
theorem toVec55_eq_toVec55Q_promotion (X : Herm2x2Os) :
    toVec55 X =
      Herm2x2OsO55RationalBridge.toVec55Q
        (InfoGeometry.Algebra.SplitOctonionIsomorphism.hermitianPromotion X) := by
  funext i
  fin_cases i <;>
    rfl

/-- The mixed-carrier `(5,5)` readout is faithful. -/
theorem toVec55_injective : Function.Injective toVec55 := by
  intro X Y h
  apply InfoGeometry.Algebra.SplitOctonionIsomorphism.hermitianPromotion_injective
  apply Herm2x2OsO55RationalBridge.vec55Equiv.injective
  show Herm2x2OsO55RationalBridge.toVec55Q (hermitianPromotion X) =
       Herm2x2OsO55RationalBridge.toVec55Q (hermitianPromotion Y)
  rw [← toVec55_eq_toVec55Q_promotion, ← toVec55_eq_toVec55Q_promotion]
  exact h

/-- The Zorn determinant is exactly the canonical split `(5,5)` quadratic form. -/
theorem det_eq_q55_toVec55 (X : Herm2x2Os) :
    X.det = q55 (toVec55 X) := by
  calc
    X.det =
        (InfoGeometry.Algebra.SplitOctonionIsomorphism.hermitianPromotion X).det :=
      (InfoGeometry.Algebra.SplitOctonionIsomorphism.det_preserved X).symm
    _ = q55
        (Herm2x2OsO55RationalBridge.toVec55Q
          (InfoGeometry.Algebra.SplitOctonionIsomorphism.hermitianPromotion X)) :=
      Herm2x2OsO55RationalBridge.det_eq_q55_toVec55Q _
    _ = q55 (toVec55 X) := by
      rw [toVec55_eq_toVec55Q_promotion]

/-- The same compatibility with the orientation used by the quadratic-form API. -/
theorem q55_toVec55_eq_det (X : Herm2x2Os) :
    q55 (toVec55 X) = X.det :=
  (det_eq_q55_toVec55 X).symm

end InfoGeometry.Canonical.Herm2x2OsO55Bridge
