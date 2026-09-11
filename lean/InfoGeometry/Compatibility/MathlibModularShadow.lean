/-
InfoGeometry/Compatibility/MathlibModularShadow.lean

Compatibility shadow for Mathlib's complex-backed modular API.

This file is downstream-only and imports `Mathlib.NumberTheory.Modular`
separately from the upper-half-plane compatibility layer.
-/

import Mathlib.NumberTheory.Modular
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Compatibility.MathlibUpperHalfPlaneShadow

noncomputable section

open scoped MatrixGroups Modular

namespace InfoGeometry.Compatibility

abbrev SL2Z := SL(2, ℤ)

/-- Mathlib's modular translation generator. -/
abbrev mathlibT : SL2Z :=
  ModularGroup.T

/-- Mathlib's modular fundamental domain. -/
abbrev mathlibFD : Set MathlibUHP :=
  ModularGroup.fd

/-- Mathlib's open modular fundamental domain. -/
abbrev mathlibFDo : Set MathlibUHP :=
  ModularGroup.fdo

/-- Mathlib's elliptic point `i`. -/
abbrev mathlibI : MathlibUHP :=
  UpperHalfPlane.I

/--
Projective action shadow for `SL(2,ℤ)`.

This lives in the modular shadow file so the rank-one compatibility layer can
stay continuous-only. The theorem is stated at the operator-lift level, not
as a coordinate comparison.
-/
theorem smul_shadow_SL2Z
    (g : SL2Z) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) :
    realToMathlibUHP (g • τ) =
      realToMathlibUHP
        ((InfoGeometry.Algebraic.sl2zToSL2R g : InfoGeometry.Geometry.SL2R) • τ) := by
  rfl

end InfoGeometry.Compatibility
