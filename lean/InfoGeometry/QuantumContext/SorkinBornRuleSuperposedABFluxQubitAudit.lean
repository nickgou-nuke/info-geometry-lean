/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.SorkinBornRuleSuperposedABFluxQubit

/-!
# Concrete Integer Instantiation & Audit for Section 122: Sorkin Born Rule & Superposed AB Flux Qubit
Target: `InfoGeometry/QuantumContext/SorkinBornRuleSuperposedABFluxQubitAudit.lean`

Verifies over `ℤ` (`decide`) that triple-slit intensities are non-trivial (`I₁₂₃ = 113`),
the third-order Sorkin parameter `κ₃` vanishes identically, and the superposed flux qubit readout
evaluates to exact values.
-/

namespace InfoGeometry.QuantumContext.SorkinFluxQubitAudit

open InfoGeometry.QuantumContext.SorkinFluxQubit

/-- Concrete verification of triple-slit interference (`I₁₂₃ = 149`) and `κ₃ = 0` over `ℤ`. -/
theorem sample_triple_slit_sorkin_kappa3_int :
    let ψ₁ : FresnelWave ℤ := ⟨3, 4⟩
    let ψ₂ : FresnelWave ℤ := ⟨1, 2⟩
    let ψ₃ : FresnelWave ℤ := ⟨3, 2⟩
    FresnelWave.intensity ψ₁ = 25 ∧
    FresnelWave.intensity ψ₂ = 5 ∧
    FresnelWave.intensity ψ₃ = 13 ∧
    FresnelWave.doubleSlitIntensity ψ₁ ψ₂ = 52 ∧
    FresnelWave.doubleSlitIntensity ψ₂ ψ₃ = 32 ∧
    FresnelWave.doubleSlitIntensity ψ₃ ψ₁ = 72 ∧
    FresnelWave.tripleSlitIntensity ψ₁ ψ₂ ψ₃ = 113 ∧
    FresnelWave.sorkinKappa3 ψ₁ ψ₂ ψ₃ = 0 := by
  decide

/-- Concrete verification of superposed flux qubit readout over `ℤ` with `w₊ = 2, w₋ = -1` (`w₊ + w₋ = 1`). -/
theorem sample_superposed_flux_qubit_readout_int :
    let ψ₁ : FresnelWave ℤ := ⟨3, 4⟩
    let ψ₂ : FresnelWave ℤ := ⟨1, 2⟩
    FresnelWave.superposedFluxProb ψ₁ ψ₂ 0 1 2 (-1) = 42 ∧
    FresnelWave.intensity ψ₁ + FresnelWave.intensity ψ₂ +
      2 * (2 - (-1)) * 1 * FresnelWave.yinH ψ₁ ψ₂ = 42 := by
  decide

end InfoGeometry.QuantumContext.SorkinFluxQubitAudit
