import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# Normalization bridge for the `(5,5)` exterior-spinor carrier

The exterior-spinor owner uses the symmetric pairing normalized as
`(ξ y + η x) / 2`.  The generic neutral phase-space owner stores the same
geometry as the bilinear form `ξ y + η x` and its unscaled quadratic form
`ξ x`.  This file records the exact factor-of-two bridge once, so downstream
Clifford/pure-spinor consumers do not repeat normalization calculations.
-/

namespace InfoGeometry.Clifford.SplitClifford55NeutralPairingBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

abbrev PhaseSpace55 := PhaseSpaceCarrier V5

theorem neutralPairing_eq_half_canonicalNeutralBilin
    (w z : PhaseSpace55) :
    neutralPairing w z =
      (1 / 2 : ℝ) * canonicalNeutralBilin (E := V5) w z := by
  rcases w with ⟨v, φ⟩
  rcases z with ⟨u, ψ⟩
  simp [neutralPairing, canonicalNeutralBilin_apply]
  ring

theorem neutralPairing_self_eq_canonicalNeutralFormUnscaled
    (w : PhaseSpace55) :
    neutralPairing w w =
      canonicalNeutralFormUnscaled (E := V5) w := by
  rw [neutralPairing_eq_half_canonicalNeutralBilin]
  simp [canonicalNeutralFormUnscaled_apply]
  ring

theorem neutralAction_anticommutator_eq_canonicalNeutralBilin
    (w z : PhaseSpace55) :
    neutralAction w * neutralAction z + neutralAction z * neutralAction w =
      canonicalNeutralBilin (E := V5) w z •
        (1 : SpinorEnd) := by
  rw [neutralAction_anticommutator]
  rw [neutralPairing_eq_half_canonicalNeutralBilin]
  congr 1
  ring

end InfoGeometry.Clifford.SplitClifford55NeutralPairingBridge
