import InfoGeometry.Canonical.BostConnesPhaseTransition
import InfoGeometry.Canonical.PauliWorldClockSynchronicity

/-!
# Bost-Connes zeta-phase readout and Pauli synchronicity

This module packages the finite low-temperature Bost-Connes readout together
with the proved Pauli world-clock synchronicity invariant. It does not claim a
global KMS classification or any zeta-pole phase transition theorem beyond the
imported finite results.
-/

namespace InfoGeometry.Canonical.BostConnesZetaPhase

/-- A finite zeta-phase carrier recording the low-temperature Gibbs readout and
the Pauli synchronicity invariant. -/
structure ZetaPhaseData (R : Type*) [CommRing R] (clock : PauliWorldClock R)
    (β : ℝ) where
  hβ : 1 < β
  partition_eq : InfoGeometry.Canonical.BostConnesKMS.bostConnesPartition β =
      (riemannZeta (β : ℂ)).re
  mass_one : (∑' n : ℕ+,
      InfoGeometry.Canonical.BostConnesKMS.normalizedBostConnesWeight β n) = 1
  positivity : ∀ n : ℕ+,
      0 < InfoGeometry.Canonical.BostConnesKMS.normalizedBostConnesWeight β n
  synchronicity :
      clock.red_wheel.e * clock.red_wheel.u =
        clock.green_wheel.e * clock.green_wheel.u ∧
      clock.green_wheel.e * clock.green_wheel.u =
        clock.blue_wheel.e * clock.blue_wheel.u

/-- The finite low-temperature Bost-Connes readout together with the proved
Pauli synchronicity invariant. -/
theorem zetaPhaseCarrier_exists
    (R : Type*) [CommRing R] (clock : PauliWorldClock R) (β : ℝ) (hβ : 1 < β) :
    ZetaPhaseData R clock β := by
  rcases InfoGeometry.Canonical.bostConnes_pauli_synchronicity_package clock β hβ with
    ⟨hLow, hPart, hMass, hPos, hSync⟩
  exact
    ⟨hLow, hPart, hMass, hPos, hSync⟩

end InfoGeometry.Canonical.BostConnesZetaPhase
