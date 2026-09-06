import InfoGeometry.Topology.ActualXiHardyZRealizationBridge
import InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge

/-!
# Actual entire-Xi real readout

This owner instantiates the finite real-readout interface with the native
pole-removed `entireRiemannXi`.  The resulting real function is the critical
line readout of `entireRiemannXi`; it is not asserted to be the classical
Hardy `Z` function, whose phase normalization is separate analytic data.
-/

noncomputable section

namespace InfoGeometry.Topology.ActualEntireXiRealReadoutBridge

open InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge
open InfoGeometry.Topology.ActualXiHardyZRealization
open InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge

/-- The actual entire-Xi real readout with unit normalization factor. -/
def actualEntireRiemannXiRealReadoutDatum :
    ConcreteHardyZDatum where
  Z := criticalLineRealReadout entireRiemannXi
  r := fun _ => 1
  r_ne_zero := by intro t; norm_num
  Xi_eval := fun t => entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
  Xi_eq_r_mul_Z := by
    intro t
    simpa using
      (criticalLineRealReadout_eq_xi entireRiemannXi
        actualEntireRiemannXiFunctionDatum t).symm

theorem actualEntireRiemannXiRealReadout_even (t : ℝ) :
    actualEntireRiemannXiRealReadoutDatum.Z (-t) =
      actualEntireRiemannXiRealReadoutDatum.Z t := by
  change criticalLineRealReadout entireRiemannXi (-t) =
    criticalLineRealReadout entireRiemannXi t
  simpa [criticalLineRealReadout] using
    congrArg Complex.re (entireRiemannXi_criticalLine_even t)

theorem actualEntireRiemannXiRealReadout_zero_iff (t : ℝ) :
    actualEntireRiemannXiRealReadoutDatum.Xi_eval t = 0 ↔
      actualEntireRiemannXiRealReadoutDatum.Z t = 0 := by
  exact hardy_z_zero_equivalence actualEntireRiemannXiRealReadoutDatum t

end InfoGeometry.Topology.ActualEntireXiRealReadoutBridge
