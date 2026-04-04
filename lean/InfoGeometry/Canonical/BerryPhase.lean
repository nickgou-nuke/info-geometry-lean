import InfoGeometry.Canonical.BerryConnection
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

/--
Certified Information Berry Phase `γ`.
This is the proof-carrying refinement of `informationBerryPhase`, computed from
a certified chiral spectral triple.
-/
noncomputable def certifiedInformationBerryPhase
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E) : ℝ :=
  (L.N : ℝ) * certifiedChiralAnomalyIndex CCST

/-- Topological anomaly flux enclosed by a Bayesian loop. -/
noncomputable def anomalyFlux (L : BayesianLoop E) (CST : ChiralSpectralTriple E) : ℝ :=
  (L.N : ℝ) * chiralAnomalyIndex CST

/-- Certified topological anomaly flux enclosed by a Bayesian loop. -/
noncomputable def certifiedAnomalyFlux
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E) : ℝ :=
  (L.N : ℝ) * certifiedChiralAnomalyIndex CCST

/--
The certified Berry phase agrees with the witness-level Berry phase after
forgetting certification.
-/
theorem certifiedInformationBerryPhase_eq_informationBerryPhase
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E) :
    certifiedInformationBerryPhase L CCST
      = informationBerryPhase L CCST.toChiralSpectralTriple := by
  simp [certifiedInformationBerryPhase, informationBerryPhase,
    certifiedChiralAnomalyIndex_eq_chiralAnomalyIndex]

/--
The certified anomaly flux agrees with the witness-level anomaly flux after
forgetting certification.
-/
theorem certifiedAnomalyFlux_eq_anomalyFlux
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E) :
    certifiedAnomalyFlux L CCST = anomalyFlux L CCST.toChiralSpectralTriple := by
  simp [certifiedAnomalyFlux, anomalyFlux,
    certifiedChiralAnomalyIndex_eq_chiralAnomalyIndex]

/-- Expanded form: certified Berry phase equals loop length times the certified chiral anomaly index. -/
theorem certifiedInformationBerryPhase_eq_loopLength_mul_certifiedChiralAnomalyIndex
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E) :
    certifiedInformationBerryPhase L CCST = (L.N : ℝ) * certifiedChiralAnomalyIndex CCST := by
  rfl

/-- Expanded form: certified Berry phase equals loop length times `ε` times certified spectral projector rank. -/
theorem certifiedInformationBerryPhase_eq_loopLength_mul_epsilon_mul_rank
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E) :
    certifiedInformationBerryPhase L CCST
      = (L.N : ℝ) * CCST.epsilon *
          (Module.finrank ℝ
            (LinearMap.range CCST.toCertifiedInverseKernel.spectralProjector.toLinearMap) : ℝ) := by
  simp [certifiedInformationBerryPhase, certifiedChiralAnomalyIndex, mul_assoc]

/-- Nonzero loop length and certified anomaly index force nonzero certified Berry phase. -/
theorem certifiedInformationBerryPhase_ne_zero_of_loopLength_ne_zero_of_certifiedChiralAnomalyIndex_ne_zero
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E)
    (hLoop : (L.N : ℝ) ≠ 0)
    (hIdx : certifiedChiralAnomalyIndex CCST ≠ 0) :
    certifiedInformationBerryPhase L CCST ≠ 0 := by
  simpa [certifiedInformationBerryPhase] using mul_ne_zero hLoop hIdx

/-- Nontrivial certified anomaly flux implies nontrivial certified Berry holonomy. -/
theorem certifiedBerryPhase_ne_zero_of_certifiedAnomalyFlux_ne_zero
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E)
    (hFlux : certifiedAnomalyFlux L CCST ≠ 0) :
    certifiedInformationBerryPhase L CCST ≠ 0 := by
  simpa [certifiedInformationBerryPhase, certifiedAnomalyFlux] using hFlux

/--
Commuting certified spectral and metric projectors force the certified Berry
phase to vanish.
-/
theorem certifiedInformationBerryPhase_eq_zero_of_projectors_commute
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E)
    (hComm :
      CCST.spectralProjector * CCST.metricProjector
        = CCST.metricProjector * CCST.spectralProjector) :
    certifiedInformationBerryPhase L CCST = 0 := by
  simp [certifiedInformationBerryPhase,
    certifiedChiralAnomalyIndex_eq_zero_of_projectors_commute, hComm]

/--
Commuting certified spectral and metric projectors force the certified anomaly
flux to vanish.
-/
theorem certifiedAnomalyFlux_eq_zero_of_projectors_commute
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E)
    (hComm :
      CCST.spectralProjector * CCST.metricProjector
        = CCST.metricProjector * CCST.spectralProjector) :
    certifiedAnomalyFlux L CCST = 0 := by
  simp [certifiedAnomalyFlux,
    certifiedChiralAnomalyIndex_eq_zero_of_projectors_commute, hComm]

/-- Expanded form: Berry phase equals loop length times the chiral anomaly index. -/
theorem informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E) :
    informationBerryPhase L CST = (L.N : ℝ) * chiralAnomalyIndex CST := by
  rfl

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

/--
Commuting witness-level spectral and metric projectors force the Berry phase to
vanish.
-/
theorem informationBerryPhase_eq_zero_of_projectors_commute
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (hComm :
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD
          * IsMoorePenroseInverse.leftProjector CST.D CST.DP
        = IsMoorePenroseInverse.leftProjector CST.D CST.DP
          * InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD) :
    informationBerryPhase L CST = 0 := by
  simp [informationBerryPhase, chiralAnomalyIndex_eq_zero_of_projectors_commute, hComm]

/--
Commuting witness-level spectral and metric projectors force the anomaly flux to
vanish.
-/
theorem anomalyFlux_eq_zero_of_projectors_commute
    (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (hComm :
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD
          * IsMoorePenroseInverse.leftProjector CST.D CST.DP
        = IsMoorePenroseInverse.leftProjector CST.D CST.DP
          * InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD) :
    anomalyFlux L CST = 0 := by
  simp [anomalyFlux, chiralAnomalyIndex_eq_zero_of_projectors_commute, hComm]

omit [FiniteDimensional ℝ E] in
/-- The Berry phase vanishes on normal belief manifolds. -/
theorem berry_phase_vanishes_for_normal (L : BayesianLoop E) (CST : ChiralSpectralTriple E)
    (h_normal : chiralScale CST.D CST.DD CST.DP = 0) :
    informationBerryPhase L CST = 0 := by
  simp [informationBerryPhase, chiralAnomalyIndex, ChiralSpectralTriple.epsilon, h_normal]

/-- The certified Berry phase vanishes on normal belief manifolds. -/
theorem certifiedBerryPhase_vanishes_for_normal
    (L : BayesianLoop E) (CCST : CertifiedChiralSpectralTriple E)
    (h_normal : chiralScale CCST.D CCST.DD CCST.DP = 0) :
    certifiedInformationBerryPhase L CCST = 0 := by
  rw [certifiedInformationBerryPhase_eq_informationBerryPhase]
  simpa using
    berry_phase_vanishes_for_normal
      (L := L)
      (CST := CCST.toChiralSpectralTriple)
      h_normal

end InfoGeometry.Canonical.BerryPhase
