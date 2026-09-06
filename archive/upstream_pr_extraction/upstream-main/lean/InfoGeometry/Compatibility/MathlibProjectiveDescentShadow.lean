/-
InfoGeometry/Compatibility/MathlibProjectiveDescentShadow.lean

Compatibility shadow for Mathlib's complex-backed projective descent.

This file is downstream-only. The real core does not import it.
-/

import InfoGeometry.Canonical.PSLDescent

noncomputable section

namespace InfoGeometry.Compatibility

open UpperHalfPlane

/--
The `SL(2,ℝ)` action on Mathlib's complex upper half-plane is insensitive to
central sign.
-/
theorem sl2r_neg_smul
    (g : InfoGeometry.Canonical.PSLDescent.SL2R)
    (τ : UpperHalfPlane) :
    (-g) • τ = g • τ :=
  InfoGeometry.Canonical.PSLDescent.sl2r_neg_smul g τ

/--
The integer modular subgroup has the same kernel-triviality on the base action.
-/
theorem sl2z_neg_smul
    (g : InfoGeometry.Canonical.PSLDescent.SL2Z)
    (τ : UpperHalfPlane) :
    (-g) • τ = g • τ :=
  InfoGeometry.Canonical.PSLDescent.sl2z_neg_smul g τ

end InfoGeometry.Compatibility
