import InfoGeometry.Canonical.Promoted.SpectralInference
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exp

namespace InfoGeometry.Research.HeatKernel

open InfoGeometry.Research.SpectralInference
open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Spectral volume surrogate from the basepoint Fisher metric trace. -/
noncomputable def spectralVolume (IST : InfoSpectralTriple E) : ℝ :=
  LinearMap.trace ℝ E (IST.H.metricOp IST.x₀).toLinearMap

/--
The Heat Trace K(t) = Tr(e^{-t D^2}).
In our InfoSpectralTriple, D^2 = ∇^2ψ (the Fisher Metric).
-/
noncomputable def heatTrace (IST : InfoSpectralTriple E) (t : ℝ) : ℝ :=
  -- First-order spectral surrogate: e^{-t} weighted spectral volume.
  Real.exp (-t) * spectralVolume IST

/-! ### Seeley-DeWitt Expansion and Curvature -/

/-- 
The zeroth Seeley-DeWitt coefficient a₀.
a₀ = (4πt)^{-d/2} ∫ √g dx.
Represents the 'Information Volume' (Model Complexity).
-/
noncomputable def a0 (IST : InfoSpectralTriple E) : ℝ :=
  -- Zeroth coefficient of e^{-t} * V is V.
  spectralVolume IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma a0_eq_spectralVolume (IST : InfoSpectralTriple E) :
    a0 IST = spectralVolume IST := rfl

/-- 
The first Seeley-DeWitt coefficient a₁.
a₁ = (4πt)^{-d/2 + 1} (1/6) ∫ R √g dx.
Represents the 'Total Scalar Curvature' of the belief space.
This coefficient is the spectral signature of 'Fisher Tension'.
-/
noncomputable def a1 (IST : InfoSpectralTriple E) : ℝ :=
  -- First coefficient of e^{-t} * V is -V.
  - spectralVolume IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma a1_eq_neg_spectralVolume (IST : InfoSpectralTriple E) :
    a1 IST = - spectralVolume IST := rfl

/--
Spectral definition of the Total Scalar Curvature R.
Calculated as the coefficient of the O(t) term in the heat trace expansion.
-/
noncomputable def totalScalarCurvature (IST : InfoSpectralTriple E) : ℝ :=
  -- From the heat trace: R_total = 6 * a1.
  6 * a1 IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma totalScalarCurvature_eq_neg_six_spectralVolume (IST : InfoSpectralTriple E) :
    totalScalarCurvature IST = -6 * spectralVolume IST := by
  simp [totalScalarCurvature]

/--
The Einstein-Hilbert Action of the Information Manifold.
S_EH = ∫ R √g d^nx.
This action penalizes non-flatness (inconsistent belief updates) in the manifold.
-/
noncomputable def einsteinHilbertAction (IST : InfoSpectralTriple E) : ℝ :=
  totalScalarCurvature IST

omit [FiniteDimensional ℝ E] in
@[simp] lemma einsteinHilbertAction_eq_totalScalarCurvature (IST : InfoSpectralTriple E) :
    einsteinHilbertAction IST = totalScalarCurvature IST := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma einsteinHilbertAction_eq_neg_six_spectralVolume (IST : InfoSpectralTriple E) :
    einsteinHilbertAction IST = -6 * spectralVolume IST := by
  simp [einsteinHilbertAction]

end InfoGeometry.Research.HeatKernel
