/- 
InfoGeometry/Geometry/RealUpperHalfPlane.lean

Pure real substrate for the modular/projective bridge.

This file contains the real half-plane model and the positive-height cusp ray.
It does not import any complex-analysis or upper-half-plane compatibility layer.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace InfoGeometry.Geometry

/-- The real upper half-plane as a positive-height real coordinate plane. -/
@[ext]
structure RealUpperHalfPlane where
  x : ℝ
  y : ℝ
  y_pos : 0 < y

/-- Positive real height parameter for cusp rays. -/
abbrev PosReal := { y : ℝ // 0 < y }

/-- The vertical cusp ray, written purely in real coordinates. -/
def verticalRay (Y : PosReal) : RealUpperHalfPlane where
  x := 0
  y := Y
  y_pos := Y.property

namespace RealUpperHalfPlane

/-- The real point corresponding to the elliptic point usually written `i`. -/
def ellipticI : RealUpperHalfPlane :=
  { x := 0, y := 1, y_pos := by norm_num }

/--
The left elliptic point, matching Mathlib's `UpperHalfPlane.ρ` convention:
`(-1/2, sqrt 3 / 2)`.
-/
noncomputable def ellipticRhoLeft : RealUpperHalfPlane :=
  { x := -(1 : ℝ) / 2,
    y := Real.sqrt 3 / 2,
    y_pos := by
      have h : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
      linarith }

/--
The right elliptic corner `(1/2, sqrt 3 / 2)`, conjugate to the left one
by the translation side-pairing.
-/
noncomputable def ellipticRhoRight : RealUpperHalfPlane :=
  { x := (1 : ℝ) / 2,
    y := Real.sqrt 3 / 2,
    y_pos := by
      have h : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
      linarith }

/-- Default compatibility convention: match Mathlib's `UpperHalfPlane.ρ`. -/
noncomputable abbrev ellipticRho : RealUpperHalfPlane :=
  ellipticRhoLeft

end RealUpperHalfPlane

end InfoGeometry.Geometry
