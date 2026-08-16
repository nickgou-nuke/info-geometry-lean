import Mathlib.Tactic
import InfoGeometry.Canonical.DrazinCentralizerErlangen
import InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket
import InfoGeometry.Arithmetic.RHQuantumStabilityBridge

/-!
# InfoGeometry.Canonical.DrazinMajoranaMellinCalibration

Thin calibration packet connecting the Drazin/Fierz centralizer surface to the
Majorana/Mellin critical-line surface.

This module does not claim a new analytic equivalence.  It packages an explicit
compatibility property between:

* the Drazin expectation readout carried by `FinalDrazinFierzLaw`;
* the Majorana zero-mode normalizability packet;
* the Mellin/Plancherel critical-line packet.

The theorem content is limited to readback along the supplied calibration fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinMajoranaMellinBridge

open InfoGeometry.Canonical.DrazinCentralizerErlangen
open InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

/--
Calibration packet for the Drazin centralizer and Majorana/Mellin sector.

`scalarReadout` is the shared scalar target used to identify the real part of
the Drazin readout with the Majorana and Mellin real parts.
-/
@[rep_depth operator]
structure DrazinMajoranaMellinCalibration
    (Obs ZeroMode NormReadout MellinWave MellinNorm : Type)
    [Ring Obs] [Star Obs] [SMul ℂ Obs] where
  drazin :
    InfoGeometry.Canonical.DrazinCentralizerErlangen.FinalDrazinFierzLaw Obs
  majorana :
    MajoranaZeroModeNormalizabilityData ZeroMode NormReadout
  mellin :
    MellinPlancherelCriticalLineData MellinWave MellinNorm
  channel :
    InfoGeometry.Canonical.DrazinFierzBridge.FierzChannel
  scalarReadout : ℝ
  drazin_readout :
    scalarReadout =
      (drazin.coords.coord channel).re
  majorana_readout :
    scalarReadout = majorana.realPart
  mellin_readout :
    majorana.realPart = mellin.realPart

namespace DrazinMajoranaMellinCalibration

variable {Obs ZeroMode NormReadout MellinWave MellinNorm : Type}
variable [Ring Obs] [Star Obs] [SMul ℂ Obs]
variable (B : DrazinMajoranaMellinCalibration
  Obs ZeroMode NormReadout MellinWave MellinNorm)

/-- The Drazin readout and the Majorana real part coincide under calibration. -/
@[rep_depth operator]
theorem drazin_readout_eq_majorana_realPart :
    (B.drazin.coords.coord B.channel).re = B.majorana.realPart := by
  rw [← B.drazin_readout, B.majorana_readout]

/-- The Drazin readout and the Mellin real part coincide under calibration. -/
@[rep_depth operator]
theorem drazin_readout_eq_mellin_realPart :
    (B.drazin.coords.coord B.channel).re = B.mellin.realPart := by
  rw [← B.drazin_readout, B.majorana_readout, B.mellin_readout]

/-- The shared scalar readout lies on the critical line by the Majorana owner field. -/
@[rep_depth operator]
theorem scalarReadout_on_criticalLine :
    InfoGeometry.Arithmetic.RHQuantumStabilityBridge.IsCriticalLineRealPart
      B.scalarReadout := by
  simpa [B.majorana_readout] using B.majorana.criticalLine

end DrazinMajoranaMellinCalibration

end InfoGeometry.Canonical.DrazinMajoranaMellinBridge
