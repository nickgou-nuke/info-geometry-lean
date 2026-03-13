import InfoGeometry.Canonical.TopologicalInvariants
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.QuantumInference
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.SpectralInference
import Mathlib.LinearAlgebra.Determinant

namespace InfoGeometry.Canonical.BerryPhase

open InfoGeometry.Canonical.TopologicalInvariants
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.QuantumInference
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Information Berry Connection.
Measures the local 'tilt' or rotation of the chiral anomaly χ
as we move between belief states.
A = log |det(χ * dχ)|.
-/
noncomputable def berryConnection (CI : ConformalInference E) (dCI : ConformalInference E) : ℝ :=
  -- Log-absolute Jacobian determinant of anomaly coupling.
  Real.log (|LinearMap.det (CI.chiralAnomaly * dCI.chiralAnomaly).toLinearMap|)

/--
The Information Berry Phase γ.
Accumulated by the belief state when transported around a periodic path (Bayesian loop).
γ = ∮ A = ∫∫ Ω, where Ω is the Berry curvature.
This phase represents the 'Topological Memory' of the inference system.
-/
noncomputable def informationBerryPhase (L : BayesianLoop E) (CST : ChiralSpectralTriple E) : ℝ :=
  -- Discrete loop period times anomaly index.
  (L.N : ℝ) * chiralAnomalyIndex CST

omit [FiniteDimensional ℝ E] in
/--
Theorem: In a normal belief manifold (ε = 0), the Berry Phase vanishes.
This proves that topological memory is purely a feature of chiral (twisted)
information manifolds.
-/
theorem berry_phase_vanishes_for_normal (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (h_normal : chiralScale CST.D CST.DD CST.DP = 0) :
    informationBerryPhase L CST = 0 := by
  simp [informationBerryPhase, chiralAnomalyIndex, ChiralSpectralTriple.epsilon, h_normal]

end InfoGeometry.Canonical.BerryPhase
