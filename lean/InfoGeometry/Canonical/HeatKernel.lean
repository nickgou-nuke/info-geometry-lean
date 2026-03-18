import InfoGeometry.Canonical.RicciMongeAmpere
import Mathlib.Analysis.SpecialFunctions.Exp

namespace InfoGeometry.Canonical.HeatKernel

open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- Spectral log-volume proxy from the basepoint Fisher metric Jacobian determinant. -/
noncomputable def spectralLogVolume (IST : InfoSpectralTriple E) : ℝ :=
  spectralBasepointLogVolume IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma spectralLogVolume_eq_spectralBasepointLogVolume (IST : InfoSpectralTriple E) :
    spectralLogVolume IST = spectralBasepointLogVolume IST := rfl

/--
Reduced heat-trace proxy `K(t)` in the collapsed log-volume model.
This is a scalar surrogate, not an operator trace `Tr(exp(-t D^2))`.
-/
noncomputable def heatTrace (IST : InfoSpectralTriple E) (t : ℝ) : ℝ :=
  Real.exp (-t) * spectralLogVolume IST

/-! ### Reduced Spectral Coefficients and Curvature Proxies -/

/-- 
Reduced zeroth spectral coefficient proxy.
In this collapsed model it is the basepoint spectral log-volume scalar.
-/
noncomputable def a0 (IST : InfoSpectralTriple E) : ℝ :=
  spectralLogVolume IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma a0_eq_spectralLogVolume (IST : InfoSpectralTriple E) :
    a0 IST = spectralLogVolume IST := rfl

/--
Reduced first spectral coefficient proxy.
It is defined from the already-landed spinorial scalar-curvature scalar.
-/
noncomputable def a1 (IST : InfoSpectralTriple E) : ℝ :=
  (1 / 6 : ℝ) * spinorialScalarCurvature IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma a1_eq_neg_spectralLogVolume (IST : InfoSpectralTriple E) :
    a1 IST = - spectralLogVolume IST := by
  rw [a1]
  rw [spinorialScalarCurvature_eq_neg_six_spectralBasepointLogVolume]
  ring_nf
  simp [spectralLogVolume]

/--
Integrated scalar-curvature proxy supplied by the spinorial curvature layer.
-/
noncomputable def totalScalarCurvature (IST : InfoSpectralTriple E) : ℝ :=
  spinorialScalarCurvature IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma totalScalarCurvature_eq_spinorialScalarCurvature
    (IST : InfoSpectralTriple E) :
    totalScalarCurvature IST = spinorialScalarCurvature IST := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma totalScalarCurvature_eq_neg_six_spectralLogVolume (IST : InfoSpectralTriple E) :
    totalScalarCurvature IST = -6 * spectralLogVolume IST := by
  simp [spectralLogVolume, totalScalarCurvature]

/--
Reduced Einstein-Hilbert action proxy.
In this file it is just a naming alias for the integrated scalar-curvature proxy.
-/
noncomputable def einsteinHilbertAction (IST : InfoSpectralTriple E) : ℝ :=
  totalScalarCurvature IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma einsteinHilbertAction_eq_totalScalarCurvature (IST : InfoSpectralTriple E) :
    einsteinHilbertAction IST = totalScalarCurvature IST := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma einsteinHilbertAction_eq_neg_six_spectralLogVolume (IST : InfoSpectralTriple E) :
    einsteinHilbertAction IST = -6 * spectralLogVolume IST := by
  simp [einsteinHilbertAction]

end InfoGeometry.Canonical.HeatKernel
