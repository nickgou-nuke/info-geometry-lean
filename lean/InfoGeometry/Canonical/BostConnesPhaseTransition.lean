import InfoGeometry.Algebra.BostConnesKMSPhaseTransition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BostConnesColimitKMSBridge
import InfoGeometry.Canonical.PauliWorldClockSynchronicity

/-!
# Bost-Connes low-temperature package and Pauli synchronicity bridge

This file packages the existing low-temperature Bost-Connes KMS data with the
proved Pauli world-clock synchronicity invariant.  It does not claim any
additional phase classification or carrier identification beyond the imported
owner theorems.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.BostConnesKMSPhaseTransition
open InfoGeometry.Canonical.BostConnesColimitKMSBridge

/-- The finite Bost-Connes low-temperature package. -/
theorem bostConnes_lowTemperature_package (β : ℝ) (hβ : 1 < β) :
    isLowTemperaturePhase β ∧
      InfoGeometry.Canonical.BostConnesKMS.bostConnesPartition β =
        (riemannZeta (β : ℂ)).re ∧
      (∑' n : ℕ+,
        InfoGeometry.Canonical.BostConnesKMS.normalizedBostConnesWeight β n) = 1 ∧
      ∀ n : ℕ+, 0 < InfoGeometry.Canonical.BostConnesKMS.normalizedBostConnesWeight β n := by
  simpa [isLowTemperaturePhase] using
    InfoGeometry.Canonical.BostConnesColimitKMSBridge.colimit_kms_state_exists
      (β := β) hβ

/-- The Pauli world clock keeps its proved synchronicity invariant alongside the
low-temperature Bost-Connes package. -/
theorem bostConnes_pauli_synchronicity_package
    {R : Type*} [CommRing R] (clock : PauliWorldClock R) (β : ℝ) (hβ : 1 < β) :
    isLowTemperaturePhase β ∧
      InfoGeometry.Canonical.BostConnesKMS.bostConnesPartition β =
        (riemannZeta (β : ℂ)).re ∧
      (∑' n : ℕ+,
        InfoGeometry.Canonical.BostConnesKMS.normalizedBostConnesWeight β n) = 1 ∧
      (∀ n : ℕ+,
        0 < InfoGeometry.Canonical.BostConnesKMS.normalizedBostConnesWeight β n) ∧
      clock.red_wheel.e * clock.red_wheel.u = clock.green_wheel.e * clock.green_wheel.u ∧
      clock.green_wheel.e * clock.green_wheel.u = clock.blue_wheel.e * clock.blue_wheel.u := by
  rcases bostConnes_lowTemperature_package β hβ with ⟨hLow, hPart, hMass, hPos⟩
  exact ⟨hLow, hPart, hMass, hPos, synchronicity_invariant clock⟩

end InfoGeometry.Canonical
