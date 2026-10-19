/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.Ring
import InfoGeometry.QuantumContext.AharonovBohmFresnelDivergenceResolution

/-!
# Finite Fresnel Flux-Reversal Identity

This module extends the canonical `SorkinFluxQubit.FresnelWave` owner with a
direct identity for reversing the supplied sine coordinate:
`abProb(c, -s) - abProb(c, s) = -4 s · yinH`.

This is a finite scalar-algebra theorem. It does not derive a Fresnel integral,
a physical flux path integral, or an asymptotic divergence result.
-/

namespace InfoGeometry.QuantumContext.SorkinFluxQubit.FresnelWave

variable {R : Type*} [CommRing R]

/-- Reversing the supplied sine coordinate changes the canonical Fresnel
transition expression by exactly `-4 s · yinH`. The formula is valid for
arbitrary scalar parameters; no unit-circle condition is assumed. -/
theorem ab_probability_flux_reversal_difference
    (ψ₁ ψ₂ : FresnelWave R) (c s : R) :
    abProb ψ₁ ψ₂ c (-s) - abProb ψ₁ ψ₂ c s =
      -4 * s * yinH ψ₁ ψ₂ := by
  dsimp [abProb]
  ring

end InfoGeometry.QuantumContext.SorkinFluxQubit.FresnelWave
