import InfoGeometry.Canonical.WeakValueEnstrophy
import InfoGeometry.Canonical.KreinSeamEvolution
import InfoGeometry.Canonical.WeakValueCylinderTransport
import InfoGeometry.Canonical.WeakValueForcedShear

/-! Regression proofs for cancellation, spatial vorticity, and the seam domain.
These examples must be compiled on the pinned toolchain before approval.
-/

noncomputable section
namespace InfoGeometry.Canonical.WeakValueReconstructionChecks

open MeasureTheory
open WeakValueSpatialReconstruction WeakValueEnstrophy

/-- Vanishing numerator and denominator at the same rate need not amplify. -/
example (d : ℝ) (hd : d ≠ 0) : d / d = 1 := div_self hd

/-- An imaginary weak pole need not have a divergent real velocity. -/
example (d : ℝ) : (Complex.I / (d : ℂ)).re = 0 := by
  simp [Complex.div_re]

/-- Spatially constant fields have zero curl even at large velocity amplitude. -/
example (v : Fin 3 → ℝ) (x : Space) : curl (fun _ => v) x = 0 := by
  funext i
  fin_cases i <;> simp [curl, partial]

/-- A concrete nonzero spatial curl used to check that the integral theorem
does not silently rely on a constant-velocity proxy. -/
example (x : Space) : curl WeakValueForcedShear.current x = ![0, 0, 1] :=
  WeakValueForcedShear.current_curl x

example (mu : Measure Space) [IsProbabilityMeasure mu] (T : ℝ) :
    Filter.Tendsto
      (fun t => enstrophy mu (WeakValueForcedShear.velocity T t))
      (nhdsWithin T (Set.Iio T)) Filter.atTop :=
  WeakValueForcedShear.velocity_enstrophy_blowup mu T

example : WeakValueCylinderTransport.guardedDivision 1 0 = none := by
  simp [WeakValueCylinderTransport.guardedDivision]

end InfoGeometry.Canonical.WeakValueReconstructionChecks
