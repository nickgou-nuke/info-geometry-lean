import InfoGeometry.Canonical.ActualXiConcreteParityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Topology.ActualXiHardyZRealizationBridge

/-!
# Actual critical-line real-readout datum

This owner packages the proved real-valued critical-line readout of the
concrete `riemannXi` into the existing `ConcreteHardyZDatum` interface.
It deliberately does not construct the classical Riemann--Siegel phase or
claim an identification with the classical Hardy `Z` function.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualCriticalXiRealReadoutDatumBridge

open InfoGeometry.Canonical.ActualXiConcreteParityBridge
open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
open InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Topology.ActualXiHardyZRealization

def actualCriticalXiRealReadoutDatum : ConcreteHardyZDatum where
  Z := actualXiCriticalReadout
  r := fun _ => 1
  r_ne_zero := by
    intro t
    norm_num
  Xi_eval := fun t => centeredRiemannXi 0 t
  Xi_eq_r_mul_Z := by
    intro t
    rw [actualXiSymmetryDatum_concrete_criticalLine_real t]
    simp [actualXiCriticalReadout]

@[simp] theorem actualCriticalXiRealReadoutDatum_Z (t : ℝ) :
    actualCriticalXiRealReadoutDatum.Z t = actualXiCriticalReadout t :=
  rfl

@[simp] theorem actualCriticalXiRealReadoutDatum_Xi_eval (t : ℝ) :
    actualCriticalXiRealReadoutDatum.Xi_eval t = centeredRiemannXi 0 t :=
  rfl

theorem actualCriticalXiRealReadoutDatum_zero_iff_xi_zero (t : ℝ) :
    actualCriticalXiRealReadoutDatum.Z t = 0 ↔
      actualCriticalXiRealReadoutDatum.Xi_eval t = 0 := by
  exact (hardy_z_zero_equivalence actualCriticalXiRealReadoutDatum t).symm

theorem actualCriticalXiRealReadoutDatum_zero_iff_riemannXi_zero (t : ℝ) :
    actualCriticalXiRealReadoutDatum.Z t = 0 ↔
      riemannXi ((1 / 2 : ℂ) + Complex.I * t) = 0 := by
  simpa [actualCriticalXiRealReadoutDatum_Xi_eval, centeredRiemannXi] using
    actualCriticalXiRealReadoutDatum_zero_iff_xi_zero t

end InfoGeometry.Canonical.ActualCriticalXiRealReadoutDatumBridge
