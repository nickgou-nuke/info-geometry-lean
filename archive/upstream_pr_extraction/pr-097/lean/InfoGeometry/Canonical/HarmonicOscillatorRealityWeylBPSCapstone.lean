/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.HarmonicOscillatorRealityWeylBPS

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.HarmonicOscillatorRealityWeylBPS

/-- Canonical projection capstone for Harmonic Oscillator Reality & Weyl BPS module. -/
theorem harmonic_oscillator_reality_weyl_bps_canonical_capstone
    (p q α ψ σ : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (h_casimir : σ - 1 / 2 = 0) :
    (rapidityFrequency (p * q) = rapidityFrequency p + rapidityFrequency q) ∧
    (weylEvolution α 0 = 1) ∧
    ((weylEvolution α 0) * ψ = ψ) ∧
    (σ = 1 / 2) :=
  grand_harmonic_symphony_synthesis p q α ψ σ hp hq h_casimir

end InfoGeometry.Canonical
