/-
InfoGeometry/Compatibility/MathlibModularShadow.lean

Compatibility shadow for Mathlib's complex-backed modular API.

This file is downstream-only and imports `Mathlib.NumberTheory.Modular`
separately from the upper-half-plane compatibility layer.
-/

import Mathlib.NumberTheory.Modular
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
Minimal modular-shadow data bundle.

This is a comparison/readout package, not a core theorem.
-/
structure MathlibModularShadowContract where
  T : SL2Z
  fd : Set MathlibUHP
  fdo : Set MathlibUHP
  i : MathlibUHP

/-- The default modular-shadow bundle using Mathlib's canonical names. -/
def defaultMathlibModularShadowContract : MathlibModularShadowContract :=
  { T := mathlibT
    fd := mathlibFD
    fdo := mathlibFDo
    i := mathlibI }

/--
Witness package for the arithmetic comparison between the real and complex
modular actions.
-/
structure ArithmeticMoebiusShadowWitness where
  hreal :
    ∀ (g : SL2Z) (τ : InfoGeometry.Geometry.RealUpperHalfPlane),
      (g • τ : InfoGeometry.Geometry.RealUpperHalfPlane) =
        (InfoGeometry.Algebraic.sl2zToSL2R g : InfoGeometry.Geometry.SL2R) • τ

/--
Projective action shadow for `SL(2,ℤ)`.

This lives in the modular shadow file so the rank-one compatibility layer can
stay continuous-only. The theorem is stated at the operator-lift level, not
as a coordinate comparison.
-/
theorem smul_shadow_SL2Z
    (W : ArithmeticMoebiusShadowWitness)
    (g : SL2Z) (τ : InfoGeometry.Geometry.RealUpperHalfPlane) :
    realToMathlibUHP (g • τ) =
      realToMathlibUHP
        ((InfoGeometry.Algebraic.sl2zToSL2R g : InfoGeometry.Geometry.SL2R) • τ) := by
  exact congrArg realToMathlibUHP (W.hreal g τ)

end InfoGeometry.Compatibility
