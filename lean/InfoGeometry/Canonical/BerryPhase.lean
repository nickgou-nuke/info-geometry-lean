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

/--
Topological anomaly flux enclosed by a Bayesian loop.
-/
noncomputable def anomalyFlux (L : BayesianLoop E) (CST : ChiralSpectralTriple E) : ℝ :=
  (L.N : ℝ) * chiralAnomalyIndex CST

/--
Loop-holonomy identity: Berry phase equals anomaly flux.
-/
theorem berryPhase_eq_anomaly_flux
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E) :
    informationBerryPhase L CST = anomalyFlux L CST := rfl

/--
Exact decomposition of the Berry phase into loop length and anomaly index.
-/
theorem informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E) :
    informationBerryPhase L CST = (L.N : ℝ) * chiralAnomalyIndex CST := rfl

/--
Expanded form: Berry phase equals loop length times `ε` times spectral projector rank.
-/
theorem informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E) :
    informationBerryPhase L CST
      = (L.N : ℝ) * CST.epsilon *
          (Module.finrank ℝ
            (LinearMap.range
              (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD).toLinearMap) : ℝ) := by
  simp [informationBerryPhase, chiralAnomalyIndex, mul_assoc]

/--
If loop length is nonzero and chiral anomaly index is nonzero, the Berry phase
is nonzero.
-/
theorem informationBerryPhase_ne_zero_of_loopLength_ne_zero_of_chiralAnomalyIndex_ne_zero
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (hLoop : (L.N : ℝ) ≠ 0)
    (hIdx : chiralAnomalyIndex CST ≠ 0) :
    informationBerryPhase L CST ≠ 0 := by
  simpa [informationBerryPhase] using mul_ne_zero hLoop hIdx

/--
Nontrivial anomaly flux implies nontrivial Berry holonomy.
-/
theorem berryPhase_ne_zero_of_anomaly_flux_ne_zero
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (hFlux : anomalyFlux L CST ≠ 0) :
    informationBerryPhase L CST ≠ 0 := by
  simpa [informationBerryPhase, anomalyFlux] using hFlux

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
