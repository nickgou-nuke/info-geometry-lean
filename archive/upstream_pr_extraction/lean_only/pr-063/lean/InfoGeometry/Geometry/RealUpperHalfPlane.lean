/- 
InfoGeometry/Geometry/RealUpperHalfPlane.lean

Pure real substrate for the modular/projective bridge.

This file contains the real half-plane model and the positive-height cusp ray.
It does not import any complex-analysis or upper-half-plane compatibility layer.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace InfoGeometry.Geometry

/-
The real upper half-plane is represented below by a native product and subtype.
-/
/-- Positive real height parameter for cusp rays. -/
abbrev PosReal := { y : ℝ // 0 < y }

/-- Native product/subtype model of the real upper half-plane. -/
abbrev RealUpperHalfPlane := ℝ × PosReal

namespace RealUpperHalfPlane

abbrev x (τ : RealUpperHalfPlane) : ℝ := τ.1
abbrev y (τ : RealUpperHalfPlane) : ℝ := τ.2.1
abbrev y_pos (τ : RealUpperHalfPlane) : 0 < τ.y := τ.2.2

@[ext] theorem ext {p q : RealUpperHalfPlane}
    (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  dsimp [x, y] at hx hy
  cases hx
  cases Subtype.ext hy
  rfl

end RealUpperHalfPlane

/-- The vertical cusp ray, written purely in real coordinates. -/
def verticalRay (Y : PosReal) : RealUpperHalfPlane :=
  (0, Y)

/-- The vertical cusp ray has positive height by construction. -/
theorem verticalRay_y_pos (Y : PosReal) : 0 < (verticalRay Y).y := by
  exact Y.property

/-- The vertical cusp ray has zero horizontal coordinate. -/
theorem verticalRay_x_zero (Y : PosReal) : (verticalRay Y).x = 0 := by
  rfl

namespace RealUpperHalfPlane

/-- The real point corresponding to the elliptic point usually written `i`. -/
def ellipticI : RealUpperHalfPlane :=
  (0, ⟨1, by norm_num⟩)

/-- The elliptic point `i` has positive height. -/
theorem ellipticI_y_pos : 0 < ellipticI.y := by
  norm_num [ellipticI]

/-- The elliptic point `i` has zero horizontal coordinate. -/
theorem ellipticI_x_zero : ellipticI.x = 0 := by
  rfl

/-- The elliptic point `i` has unit height. -/
theorem ellipticI_y_eq_one : ellipticI.y = 1 := by
  rfl

/--
The left elliptic point, matching Mathlib's `UpperHalfPlane.ρ` convention:
`(-1/2, sqrt 3 / 2)`.
-/
noncomputable def ellipticRhoLeft : RealUpperHalfPlane :=
  (-(1 : ℝ) / 2, ⟨Real.sqrt 3 / 2, by
    have h : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    linarith⟩)

/-- The left elliptic corner has positive height. -/
theorem ellipticRhoLeft_y_pos : 0 < ellipticRhoLeft.y := by
  simp [ellipticRhoLeft, y]

/-- The left elliptic corner has the expected horizontal coordinate. -/
theorem ellipticRhoLeft_x_eq : ellipticRhoLeft.x = -(1 : ℝ) / 2 := by
  rfl

/-- The left elliptic corner has height `sqrt 3 / 2`. -/
theorem ellipticRhoLeft_y_eq : ellipticRhoLeft.y = Real.sqrt 3 / 2 := by
  rfl

/--
The right elliptic corner `(1/2, sqrt 3 / 2)`, conjugate to the left one
by the translation side-pairing.
-/
noncomputable def ellipticRhoRight : RealUpperHalfPlane :=
  ((1 : ℝ) / 2, ⟨Real.sqrt 3 / 2, by
    have h : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    linarith⟩)

/-- The right elliptic corner has positive height. -/
theorem ellipticRhoRight_y_pos : 0 < ellipticRhoRight.y := by
  simp [ellipticRhoRight, y]

/-- The right elliptic corner has the expected horizontal coordinate. -/
theorem ellipticRhoRight_x_eq : ellipticRhoRight.x = (1 : ℝ) / 2 := by
  rfl

/-- The right elliptic corner has height `sqrt 3 / 2`. -/
theorem ellipticRhoRight_y_eq : ellipticRhoRight.y = Real.sqrt 3 / 2 := by
  rfl

/-- Default compatibility convention: match Mathlib's `UpperHalfPlane.ρ`. -/
noncomputable abbrev ellipticRho : RealUpperHalfPlane :=
  ellipticRhoLeft

/-- The default elliptic `ρ` point has positive height. -/
theorem ellipticRho_y_pos : 0 < ellipticRho.y := by
  simpa [ellipticRho] using ellipticRhoLeft_y_pos

/-- The default elliptic `ρ` point has the expected horizontal coordinate. -/
theorem ellipticRho_x_eq : ellipticRho.x = -(1 : ℝ) / 2 := by
  simpa [ellipticRho] using ellipticRhoLeft_x_eq

/-- The default elliptic `ρ` point has height `sqrt 3 / 2`. -/
theorem ellipticRho_y_eq : ellipticRho.y = Real.sqrt 3 / 2 := by
  simpa [ellipticRho] using ellipticRhoLeft_y_eq

end RealUpperHalfPlane

end InfoGeometry.Geometry
