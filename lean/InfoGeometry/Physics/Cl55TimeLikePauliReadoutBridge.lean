import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge
import InfoGeometry.Physics.ChiralPoincareSouriauBridge

/-!
# Cl(5,5) time-like Pauli readout

The master Cl(5,5) owner proves a concrete scalar anticommutator
`{Q, Q̄} = 2 I₃₂`.  This bridge transports exactly that scalar channel to the
2-by-2 Pauli carrier.  It deliberately does not claim the full four-component
spinor relation; that requires four independently indexed supercharges.
-/

noncomputable section

namespace InfoGeometry.Physics.Cl55TimeLikePauliReadoutBridge

open Matrix
open InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge
open InfoGeometry.Physics.ChiralPoincareSouriauBridge

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- The finite scalar readout of a real `32 × 32` operator as a complex
multiple of the 2-by-2 identity. -/
def scalarPauliReadout (A : Mat32) : M2C :=
  (A default default : ℂ) • (1 : M2C)

/-- The rest-frame Pauli momentum with unit energy. -/
def unitTimeMomentum : FourMomentum :=
  ⟨1, 0, 0, 0⟩

@[simp] theorem pauli_unitTimeMomentum :
    pauliMomentum unitTimeMomentum = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitTimeMomentum, pauliMomentum]

theorem cl55_supercharge_timeLike_pauli_readout :
    scalarPauliReadout
        (superchargeQ * superchargeQBar + superchargeQBar * superchargeQ) =
      (2 : ℂ) • pauliMomentum unitTimeMomentum := by
  rw [supercharge_anticomm_momentum]
  simp [scalarPauliReadout, pauli_unitTimeMomentum]

theorem cl55_supercharge_timeLike_momentum_readout :
    scalarPauliReadout
        (superchargeQ * superchargeQBar + superchargeQBar * superchargeQ) =
      (2 : ℂ) • (1 : M2C) := by
  simpa [pauli_unitTimeMomentum] using
    cl55_supercharge_timeLike_pauli_readout

end InfoGeometry.Physics.Cl55TimeLikePauliReadoutBridge
