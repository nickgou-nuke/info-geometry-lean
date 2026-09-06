import InfoGeometry.GrandUnification.AlgebraicSouriauTomita
import InfoGeometry.GrandUnification.HodgeCartanTrifactor

/-!
# BiQuaternion Kähler Thermo Bridge

This file is deliberately finite. It does not claim an analytic hyperkähler
theory. It only packages two already-owned theorem surfaces:

* the finite Hodge/Cartan decomposition on the trifactor carrier;
* the corrected Souriau--Tomita target.

The actual phase/readout and Fisher/Hessian bridges are owned elsewhere in the
repository and are not re-stated here.
-/

noncomputable section

namespace InfoGeometry.GrandUnification.BiQuaternionKahlerThermoBridge

open InfoGeometry.GrandUnification.HodgeCartan

variable {R : Type 0} [CommRing R] [Invertible (2 : R)]
variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Finite umbrella packet for the biquaternionic/Kähler thermodynamic bridge. -/
structure BiQuaternionKahlerThermoPacket where
  /-- Hodge decomposition on the finite Cartan/tripotent carrier. -/
  hodge_decomposition :
    ∀ T : R, harmonic_op T + exact_op T + coexact_op T = 1

  /-- Souriau/Massieu finite dictionary target from the grand-unification lane. -/
  souriauTomitaTarget : InfoGeometry.GrandUnification.AlgebraicSouriauTomitaTarget

/-- Construct the umbrella packet from the already-owned theorem surfaces. -/
def constructBiQuaternionKahlerThermoPacket :
    @BiQuaternionKahlerThermoPacket R _ _ := by
  refine ⟨?_, ?_⟩
  · intro T
    exact @HodgeCartan.hodge_decomposition R _ _ T
  · exact InfoGeometry.GrandUnification.constructAlgebraicSouriauTomitaTarget

end InfoGeometry.GrandUnification.BiQuaternionKahlerThermoBridge
