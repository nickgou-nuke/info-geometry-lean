import InfoGeometry.Quantum.CelestialMellin

namespace InfoGeometry.Canonical.CelestialMellinCapstone

open InfoGeometry.Quantum.CelestialMellin

set_option linter.unusedVariables false

theorem verification_capstone (E lambda omega : ℝ) (h_omega : 0 < omega) :
    ((celestialWeight lambda).re = 1 / 2) ∧
      (1 - star (celestialWeight lambda) = celestialWeight lambda) ∧
      (‖mellinScaleFreePhase E lambda omega‖ = 1) ∧
      (IsCelestialPrimary (dilationEigenmode E) (⟨1 / 2, -E⟩)) := by
  exact grand_apollonius_celestial_mellin_synthesis E lambda omega h_omega

end InfoGeometry.Canonical.CelestialMellinCapstone
