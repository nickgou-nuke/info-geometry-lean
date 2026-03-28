import InfoGeometry.Canonical.TopologicalInvariants

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.BerryPhase

open InfoGeometry.Canonical.TopologicalInvariants
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.SpectralInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/--
The Information Berry Phase `γ`.
Accumulated by the belief state when transported around a periodic path.
-/
noncomputable def informationBerryPhase (L : BayesianLoop E) (CST : ChiralSpectralTriple E) : ℝ :=
  (L.N : ℝ) * chiralAnomalyIndex CST

/-- Topological anomaly flux enclosed by a Bayesian loop. -/
noncomputable def anomalyFlux (L : BayesianLoop E) (CST : ChiralSpectralTriple E) : ℝ :=
  (L.N : ℝ) * chiralAnomalyIndex CST

/-- Expanded form: Berry phase equals loop length times `ε` times spectral projector rank. -/
theorem informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E) :
    informationBerryPhase L CST
      = (L.N : ℝ) * CST.epsilon *
          (Module.finrank ℝ
            (LinearMap.range
              (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD).toLinearMap) : ℝ) := by
  simp [informationBerryPhase, chiralAnomalyIndex, mul_assoc]

/-- Nonzero loop length and anomaly index force nonzero Berry phase. -/
theorem informationBerryPhase_ne_zero_of_loopLength_ne_zero_of_chiralAnomalyIndex_ne_zero
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (hLoop : (L.N : ℝ) ≠ 0)
    (hIdx : chiralAnomalyIndex CST ≠ 0) :
    informationBerryPhase L CST ≠ 0 := by
  simpa [informationBerryPhase] using mul_ne_zero hLoop hIdx

/-- Nontrivial anomaly flux implies nontrivial Berry holonomy. -/
theorem berryPhase_ne_zero_of_anomaly_flux_ne_zero
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (hFlux : anomalyFlux L CST ≠ 0) :
    informationBerryPhase L CST ≠ 0 := by
  simpa [informationBerryPhase, anomalyFlux] using hFlux

omit [FiniteDimensional ℝ E] in
/-- The Berry phase vanishes on normal belief manifolds. -/
theorem berry_phase_vanishes_for_normal (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (h_normal : chiralScale CST.D CST.DD CST.DP = 0) :
    informationBerryPhase L CST = 0 := by
  simp [informationBerryPhase, chiralAnomalyIndex, ChiralSpectralTriple.epsilon, h_normal]

end InfoGeometry.Canonical.BerryPhase
