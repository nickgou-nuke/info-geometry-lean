/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.HarmonicOscillatorRealityWeylBPS
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.HarmonicOscillatorRealityWeylBPS

/-- Canonical projection of the logarithmic frequency and zero-mode BPS packet. -/
theorem harmonic_oscillator_reality_weyl_bps_canonical_capstone
    (p q α ψ σ : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (h_casimir : σ - 1 / 2 = 0) :
    (rapidityFrequency (p * q) = rapidityFrequency p + rapidityFrequency q) ∧
    (weylEvolution α 0 = 1) ∧
    ((weylEvolution α 0) * ψ = ψ) ∧
    (σ = 1 / 2) := by
  exact ⟨logarithmic_rosetta_stone p q hp hq,
    bps_shield_operator_identity α,
    bps_macroscopic_invariance α ψ,
    wigner_bps_casimir_confinement σ h_casimir⟩

end InfoGeometry.Canonical
