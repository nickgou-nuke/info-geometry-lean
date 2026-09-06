import InfoGeometry.Canonical.CantorBoundaryComplexReadout
import InfoGeometry.Canonical.CantorTwoTreeFixedLocus

/-!
# Bridge from the binary complex readout to the repository Tomita owner

This file only instantiates the pointwise-complement theorem with the
repository-owned Boolean Tomita involution.  No Stone--Gelfand equivalence is
asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryTomitaBridge

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorTwoTreeFixedLocus
open InfoGeometry.Canonical.CantorBoundaryComplexReadout

theorem binary_readout_tomita_intertwining
    (w : InfiniteBinaryWordSpace) :
    binaryReadout (tomitaWordConjugation w) + binaryReadout w = 1 := by
  exact binary_readout_intertwining_of_pointwise_complement
    tomitaWordConjugation w (fun n => rfl)

theorem binary_readout_tomita_fixed_state_on_critical_line
    (w : InfiniteBinaryWordSpace)
    (h_invariant :
      binaryReadout (tomitaWordConjugation w) = star (binaryReadout w)) :
    (binaryReadout w).re = 1 / 2 := by
  exact binary_readout_fixed_state_on_critical_line
    tomitaWordConjugation w (fun n => rfl) h_invariant

end InfoGeometry.Canonical.CantorBoundaryTomitaBridge
