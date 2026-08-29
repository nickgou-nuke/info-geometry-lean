/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.CelestialMellin

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.CelestialMellin Complex Real

/-- 🏆 GRAND CANONICAL CAPSTONE: Apollonian-Celestial Mellin Synthesis -/
theorem grand_canonical_apollonius_celestial_mellin_synthesis
    (E lambda omega : ℝ) (h_omega : 0 < omega) :
    ((celestialWeight lambda).re = 1 / 2) ∧
    (mellinKernel E lambda omega = (omega : ℂ) ^ (Complex.I * ((lambda + E : ℝ) : ℂ) - 1)) ∧
    (normSq ((omega : ℂ) ^ (Complex.I * ((lambda + E : ℝ) : ℂ))) = 1) ∧
    (IsCelestialPrimary (dilationEigenmode E) (⟨1 / 2, -E⟩)) :=
  grand_apollonius_celestial_mellin_synthesis E lambda omega h_omega

end InfoGeometry.Canonical
