import InfoGeometry.Physics.ZornScalingFlow

/-!
# The formal null boundary of the Zorn carrier

This owner records the finite algebraic facts available for the repository's
complex Zorn carrier.  It does not assert a dimension, a projectivized
homogeneous-space identification, or a `G₂` orbit theorem.
-/

namespace InfoGeometry.Canonical.SplitOctonionNullConeBoundary

open InfoGeometry.Physics.ZornScalingFlow

abbrev Zorn := InfoGeometry.Physics.ZornScalingFlow.Zorn

/-- The determinant-zero predicate for the Zorn composition norm. -/
def IsNull (X : Zorn) : Prop := zornNorm X = 0

theorem upperNil_isNull (u : Vec3) : IsNull (upperNil u) := by
  change (0 : ℂ) * 0 -
      InfoGeometry.Physics.SplitOctonionBraidSU3.dot3 u (fun _ => 0) = 0
  simp [InfoGeometry.Physics.SplitOctonionBraidSU3.dot3]

theorem lowerNil_isNull (v : Vec3) : IsNull (lowerNil v) := by
  change (0 : ℂ) * 0 -
      InfoGeometry.Physics.SplitOctonionBraidSU3.dot3 (fun _ => 0) v = 0
  simp [InfoGeometry.Physics.SplitOctonionBraidSU3.dot3]

theorem upperNil_ne_zero {u : Vec3} (hu : u ≠ 0) :
    upperNil u ≠ InfoGeometry.Physics.ZornScalingFlow.zornZero := by
  intro h
  apply hu
  funext i
  have hi := congrArg (fun X : Zorn => X.u i) h
  simpa [upperNil, InfoGeometry.Physics.ZornScalingFlow.zornZero] using hi

theorem lowerNil_ne_zero {v : Vec3} (hv : v ≠ 0) :
    lowerNil v ≠ InfoGeometry.Physics.ZornScalingFlow.zornZero := by
  intro h
  apply hv
  funext i
  have hi := congrArg (fun X : Zorn => X.v i) h
  simpa [lowerNil, InfoGeometry.Physics.ZornScalingFlow.zornZero] using hi

theorem upperNil_square_zero (u : Vec3) :
    InfoGeometry.Physics.ZornScalingFlow.zornMul (upperNil u) (upperNil u) =
      InfoGeometry.Physics.ZornScalingFlow.zornZero :=
  upperNil_sq_zero u

theorem lowerNil_square_zero (v : Vec3) :
    InfoGeometry.Physics.ZornScalingFlow.zornMul (lowerNil v) (lowerNil v) =
      InfoGeometry.Physics.ZornScalingFlow.zornZero :=
  lowerNil_sq_zero v

end InfoGeometry.Canonical.SplitOctonionNullConeBoundary
