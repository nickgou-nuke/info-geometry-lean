import Mathlib.Tactic
import Omega.SyncKernelRealInput.GMSoficZeckLinearConstraintsPF
import Omega.SyncKernelWeighted.GMResidualOpnormGramEquivalence
import Omega.SyncKernelWeighted.GMTrace3SpectralNormExtremal

namespace Omega.SyncKernelWeighted

/-- Continuous-side certificate: the residual/opnorm comparison is combined with the trace-`3`
Jensen envelope and cubic characterization from the spectral-norm extremal theorem. -/
def traceResidualCertified
    (residualData : gm_residual_opnorm_gram_equivalence_data)
    (traceMultiplicity : ℕ) (traceSum traceMoment3 spectralOffset spectralDisplacement : ℝ) : Prop :=
  let x := traceSum / (traceMultiplicity : ℝ) + spectralOffset
  let x' := traceSum / (traceMultiplicity : ℝ) + spectralDisplacement
  let y := (traceSum - x) / (traceMultiplicity - 1 : ℝ)
  gm_residual_opnorm_gram_equivalence_data.statement residualData ∧
    gmTrace3LowerEnvelope traceMultiplicity traceSum x ≤
      gmTrace3LowerEnvelope traceMultiplicity traceSum x' ∧
    (gmTrace3LowerEnvelope traceMultiplicity traceSum x = traceMoment3 ↔
      gmTrace3Cubic traceMultiplicity traceSum traceMoment3 x = 0) ∧
    x + (traceMultiplicity - 1 : ℝ) * y = traceSum ∧
    x ^ 3 + (traceMultiplicity - 1 : ℝ) * y ^ 3 =
      gmTrace3LowerEnvelope traceMultiplicity traceSum x

/-- Discrete-side certificate: the Zeckendorf/sofic additive-energy package reduces to the
finite-state Perron certificate already proven in the real-input appendix. -/
def additiveEnergyCertified : Prop :=
  Omega.SyncKernelRealInput.gm_sofic_zeck_linear_constraints_pf_statement

/-- Paper label: `thm:gm-dual-spectral-certificates`. The continuous trace-`3` residual/opnorm
certificate and the Zeckendorf/sofic finite-state Perron certificate are independent proof
streams, so the dual package is their conjunction. -/
theorem paper_gm_dual_spectral_certificates
    (residualData : gm_residual_opnorm_gram_equivalence_data)
    (traceMultiplicity : ℕ) (traceMultiplicity_ge_two : 2 ≤ traceMultiplicity)
    (traceSum traceMoment3 spectralOffset spectralDisplacement : ℝ)
    (traceSum_nonneg : 0 ≤ traceSum)
    (spectralOffset_nonneg : 0 ≤ spectralOffset)
    (spectralOffset_le_displacement : spectralOffset ≤ spectralDisplacement) :
    traceResidualCertified residualData traceMultiplicity traceSum traceMoment3
        spectralOffset spectralDisplacement ∧ additiveEnergyCertified := by
  refine ⟨?_, ?_⟩
  · dsimp [traceResidualCertified]
    refine ⟨paper_gm_residual_opnorm_gram_equivalence residualData, ?_⟩
    simpa using
      (paper_gm_trace3_spectral_norm_extremal
        traceMultiplicity
        traceMultiplicity_ge_two
        (S1 := traceSum)
        (S3 := traceMoment3)
        (u := spectralOffset)
        (v := spectralDisplacement)
        traceSum_nonneg
        spectralOffset_nonneg
        spectralOffset_le_displacement)
  · dsimp [additiveEnergyCertified]
    exact Omega.SyncKernelRealInput.paper_gm_sofic_zeck_linear_constraints_pf

end Omega.SyncKernelWeighted
