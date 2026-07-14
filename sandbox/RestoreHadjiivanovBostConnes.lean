import Mathlib
import InfoGeometry.Physics.HadjiivanovCuntzBridge
import InfoGeometry.Physics.AmplituhedronBostConnes

/-!
# RestoreHadjiivanovBostConnes

Small sandbox packet for the pure log-block partition function.
-/

namespace InfoGeometry.Restore.HadjiivanovBostConnes

open Matrix

/-- The thermodynamic KMS trace of the Hadjiivanov log block. -/
def logBlockPartitionFunction (R : Type*) [CommRing R] : R :=
  Matrix.trace (InfoGeometry.Physics.Hadjiivanov.standardLogBlock R).matrix

/-- The pure nilpotent log block has zero partition function. -/
@[simp]
theorem logBlockPartitionFunction_vanishes (R : Type*) [CommRing R] :
    logBlockPartitionFunction R = 0 := by
  simpa [logBlockPartitionFunction] using
    InfoGeometry.Physics.Hadjiivanov.standardLogBlock_trace (R := R)

/-- The bridge to the Bost-Connes KMS partition function. -/
theorem hadjiivanov_bostConnes_bridge (β : ℂ) :
    InfoGeometry.Physics.AmplituhedronBostConnes.all_loop_integrand_bost_connes_kms_state β =
      logBlockPartitionFunction ℂ + riemannZeta β := by
  rw [InfoGeometry.Physics.AmplituhedronBostConnes.all_loop_integrand_bost_connes_kms_state]
  rw [logBlockPartitionFunction_vanishes]
  simp

end InfoGeometry.Restore.HadjiivanovBostConnes
