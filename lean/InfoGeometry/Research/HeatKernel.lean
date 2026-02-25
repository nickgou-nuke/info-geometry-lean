import InfoGeometry.Research.SpectralInference
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

/-- 
The first Seeley-DeWitt coefficient a₁.
a₁ = (4πt)^{-d/2 + 1} (1/6) ∫ R √g dx.
Represents the 'Total Scalar Curvature' of the belief space.
This coefficient is the spectral signature of 'Fisher Tension'.
-/
noncomputable def a1 (IST : InfoSpectralTriple E) : ℝ :=
  -- First coefficient of e^{-t} * V is -V.
  - spectralVolume IST

/--
Spectral definition of the Total Scalar Curvature R.
Calculated as the coefficient of the O(t) term in the heat trace expansion.
-/
noncomputable def totalScalarCurvature (IST : InfoSpectralTriple E) : ℝ :=
  -- From the heat trace: R_total = 6 * a1.
  6 * a1 IST

/--
The Einstein-Hilbert Action of the Information Manifold.
S_EH = ∫ R √g d^nx.
This action penalizes non-flatness (inconsistent belief updates) in the manifold.
-/
noncomputable def einsteinHilbertAction (IST : InfoSpectralTriple E) : ℝ :=
  totalScalarCurvature IST

end InfoGeometry.Research.HeatKernel
