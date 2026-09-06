import InfoGeometry.Canonical.ActualCenteredXiDataBridge
import InfoGeometry.Canonical.ActualXiSymmetryDatumBridge

/-!
# Coordinate coherence for the concrete completed-Xi datum

This owner identifies the concrete real/imaginary `XiSymmetryDatum` readout
with the centered complex `CompletedXiData` readout.  It transports no new
analytic fact: both sides are built from Mathlib's `riemannXi`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualXiDatumCoordinateCoherence

open Complex
open InfoGeometry.Canonical.ActualCenteredXiDataBridge
open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge

theorem actualCenteredXiData_xi_real_coordinates (u tau : ℝ) :
    actualCenteredXiData.xi
        ((u : ℂ) + Complex.I * (tau : ℂ)) =
      centeredRiemannXi u tau := by
  unfold actualCenteredXiData centeredRiemannXi
  push_cast
  ring_nf

theorem actualXiSymmetryDatum_concrete_reconstruct (u tau : ℝ) :
    (actualXiSymmetryDatum_concrete.A u tau : ℂ) +
        Complex.I * (actualXiSymmetryDatum_concrete.B u tau : ℂ) =
      actualCenteredXiData.xi
        ((u : ℂ) + Complex.I * (tau : ℂ)) := by
  change (centeredRiemannXiReal u tau : ℂ) +
      Complex.I * (centeredRiemannXiImag u tau : ℂ) = _
  rw [actualCenteredXiData_xi_real_coordinates]
  apply Complex.ext <;>
    simp [centeredRiemannXiReal, centeredRiemannXiImag]

theorem actualXiSymmetryDatum_concrete_criticalLine_readout (tau : ℝ) :
    actualCenteredXiData.xi (Complex.I * (tau : ℂ)) =
      (actualXiSymmetryDatum_concrete.A 0 tau : ℂ) := by
  calc
    actualCenteredXiData.xi (Complex.I * (tau : ℂ)) =
        centeredRiemannXi 0 tau := by
      simpa using actualCenteredXiData_xi_real_coordinates 0 tau
    _ = (centeredRiemannXiReal 0 tau : ℂ) :=
      actualXiSymmetryDatum_concrete_criticalLine_real tau
    _ = (actualXiSymmetryDatum_concrete.A 0 tau : ℂ) := by
      rfl

end InfoGeometry.Canonical.ActualXiDatumCoordinateCoherence
