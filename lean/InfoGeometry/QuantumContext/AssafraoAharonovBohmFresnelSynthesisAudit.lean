/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AssafraoAharonovBohmFresnelSynthesis

/-!
# Concrete Integer Instantiation & Audit for Section 120a: Assafrão–Aharonov–Bohm–Fresnel Synthesis
Target: `InfoGeometry/QuantumContext/AssafraoAharonovBohmFresnelSynthesisAudit.lean`

Verifies over `ℤ` (`decide`) that all structures and theorems in
`InfoGeometry.QuantumContext.AssafraoABFresnel` and `InfoGeometry.QuantumContext.Jubilee120`
are non-vacuous and computationally active.
-/

namespace InfoGeometry.QuantumContext.AssafraoABFresnelAudit

open InfoGeometry.QuantumContext.AssafraoABFresnel
open InfoGeometry.QuantumContext.Jubilee120

/-- Concrete slit amplitudes `(3, 4)` and `(1, 2)` over `ℤ` satisfy the Fresnel–Lagrange identity:
`ℐ = 2*(3*1 + 4*2) = 22`, `ℋ = 2*(3*2 - 4*1) = 4`, `22^2 + 4^2 = 500 = 4 * 25 * 5`. -/
theorem sample_fresnel_lagrange_identity_int :
    let ψ_p : FresnelAmplitude ℤ := ⟨3, 4⟩
    let ψ_m : FresnelAmplitude ℤ := ⟨1, 2⟩
    FresnelAmplitude.symmInterferenceI ψ_p ψ_m = 22 ∧
    FresnelAmplitude.skewInterferenceH ψ_p ψ_m = 4 ∧
    (FresnelAmplitude.symmInterferenceI ψ_p ψ_m)^2 +
      (FresnelAmplitude.skewInterferenceH ψ_p ψ_m)^2 = 500 ∧
    4 * FresnelAmplitude.normSq ψ_p * FresnelAmplitude.normSq ψ_m = 500 := by
  decide

/-- Concrete verification of even-`π` constructive maximum (`4 * 25 = 100`) and odd-`π` null (`0`). -/
theorem sample_even_and_odd_pi_flux_int :
    let ψ₀ : FresnelAmplitude ℤ := ⟨3, 4⟩
    FresnelAmplitude.transitionProbabilityAB ψ₀ ψ₀ 1 0 = 100 ∧
    FresnelAmplitude.transitionProbabilityAB ψ₀ ψ₀ (-1) 0 = 0 ∧
    FresnelAmplitude.transitionProbabilityAB ψ₀ ψ₀ 0 1 = 50 := by
  decide

/-- Concrete verification of `Jubilee120.FresnelWave` over `ℤ`. -/
theorem sample_jubilee120_fresnel_wave_int :
    let ψ_p : FresnelWave ℤ := ⟨3, 4⟩
    let ψ_m : FresnelWave ℤ := ⟨1, 2⟩
    FresnelWave.totalProbability ψ_p ψ_p FresnelWave.zeroFluxHorizon = 100 ∧
    FresnelWave.totalProbability ψ_p ψ_p FresnelWave.piFluxCrosscap = 0 ∧
    FresnelWave.totalProbability ψ_p ψ_m ⟨0, 1⟩ -
      FresnelWave.totalProbability ψ_p ψ_m ⟨0, -1⟩ = 8 := by
  decide

end InfoGeometry.QuantumContext.AssafraoABFresnelAudit
