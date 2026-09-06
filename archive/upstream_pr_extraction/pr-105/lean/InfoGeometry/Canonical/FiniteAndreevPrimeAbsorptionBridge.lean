import InfoGeometry.Arithmetic.SymmetricPrimeLogSpectrum
import InfoGeometry.Canonical.ConcreteKitaevBdGMatrix

/-!
# Finite Andreev/prime absorption readout

This adapter reuses two independent finite owners:

* `SymmetricPrimeLogSpectrum` supplies an even finite cosine packet and its
  notch predicate;
* `ConcreteKitaevBdGMatrix` supplies particle-hole symmetry and finite
  Majorana zero-mode witnesses.

The conjunction below is deliberately only a finite readout.  It does not
identify finite notches with Riemann zeros and does not assert an analytic
scattering or absorption theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteAndreevPrimeAbsorptionBridge

open InfoGeometry.Arithmetic.SymmetricPrimeLogSpectrum
open InfoGeometry.Canonical.ConcreteKitaevBdGMatrix

theorem finitePrimeNotch_reflection_readout
    (S : Finset ℕ) (ω : ℝ)
    (hnotch : absorptionNotch S ω) :
    absorptionNotch S (-ω) ∧
      finitePrimeWaveCosine S ω = 0 := by
  constructor
  · exact (absorptionNotch_neg S ω).2 hnotch
  · exact (absorptionNotch_iff_cosine_zero S ω).mp hnotch

theorem finiteAndreevPrimeAbsorption_readout
    (S : Finset ℕ) (ω κ : ℝ)
    (hnotch : absorptionNotch S ω) :
    absorptionNotch S (-ω) ∧
      finitePrimeWaveCosine S ω = 0 ∧
      particleHole4 * particleHole4 = 1 ∧
      particleHole4 * (kitaevBdG4 0 κ κ).conjTranspose * particleHole4 =
        -kitaevBdG4 0 κ κ ∧
      Matrix.trace (kitaevBdG4 0 κ κ) = 0 ∧
      (kitaevSweetSpot4 κ).mulVec majoranaZeroModeLeft = 0 ∧
      (kitaevSweetSpot4 κ).mulVec majoranaZeroModeRight = 0 := by
  rcases finitePrimeNotch_reflection_readout S ω hnotch with ⟨hneg, hcos⟩
  exact ⟨hneg, hcos, particleHole4_square,
    kitaevBdG4_particle_hole_symmetry 0 κ κ,
    kitaevBdG4_trace_zero 0 κ κ,
    left_majorana_zero_mode_energy κ,
    right_majorana_zero_mode_energy κ⟩

end InfoGeometry.Canonical.FiniteAndreevPrimeAbsorptionBridge
