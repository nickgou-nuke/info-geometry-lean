/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AssafraoAharonovBohmFresnelSynthesis

/-!
# Concrete Integer Audit: Canonical Fresnel Flux Reversal

The integer example instantiates the sine-coordinate reversal identity on the
canonical `SorkinFluxQubit.FresnelWave` carrier. This is finite scalar algebra,
not a claim about path integrals or Fresnel asymptotics.
-/

namespace InfoGeometry.QuantumContext.AssafraoABFresnelAudit

open InfoGeometry.QuantumContext.SorkinFluxQubit
open InfoGeometry.QuantumContext.SorkinFluxQubit.FresnelWave

/-- For `(3,4)` and `(1,2)`, the Yin pairing is `2` and reversing `s=1`
changes the defined expression from `34` to `26`, hence by `-8`. -/
theorem sample_flux_reversal_int :
    let ψ₁ : FresnelWave ℤ := ⟨3, 4⟩
    let ψ₂ : FresnelWave ℤ := ⟨1, 2⟩
    yinH ψ₁ ψ₂ = 2 ∧
      abProb ψ₁ ψ₂ 0 (-1) = 26 ∧
      abProb ψ₁ ψ₂ 0 1 = 34 ∧
      abProb ψ₁ ψ₂ 0 (-1) - abProb ψ₁ ψ₂ 0 1 = -8 := by
  decide

#print axioms ab_probability_flux_reversal_difference
#print axioms sample_flux_reversal_int

end InfoGeometry.QuantumContext.AssafraoABFresnelAudit
