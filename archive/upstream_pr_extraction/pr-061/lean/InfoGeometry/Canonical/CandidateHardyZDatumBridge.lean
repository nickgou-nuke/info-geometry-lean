import InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
import InfoGeometry.Canonical.HardyZRealizationBridge

/-!
# Candidate Hardy-Z datum from the actual completed xi readout

This file packages the repository's existing `candidateHardyZ` and
`actualXiCriticalReadout` into the abstract `HardyZDatum` interface.

The construction is deliberately named `candidate`: it is a native
normalization readout of `riemannXi`, not an identification with the
classical Hardy `Z` function or with a Riemann--Siegel phase.
-/

noncomputable section

namespace InfoGeometry.Canonical.CandidateHardyZDatumBridge

open InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
open InfoGeometry.Canonical.HardyZ
open InfoGeometry.Topology.XiHardyZNormalizationBridge

def candidateHardyZDatum : HardyZDatum where
  theta := fun _ => 0
  Z := fun t => -candidateHardyZ t
  zeta_crit := fun t => (-(candidateHardyZ t) : ℂ)
  xi_crit := fun t => (actualXiCriticalReadout t : ℂ)
  scale_factor := fun t => -hardyNormalizationFactor t
  scale_pos := fun t => neg_pos.mpr (hardyNormalizationFactor_neg t)
  h_hardy_def := by
    intro t
    simp
  h_even := by
    intro t
    simp [candidateHardyZ_neg]
  h_xi_Z := by
    intro t
    have hfactor := actualXiCriticalReadout_eq_factor_mul_candidateHardyZ t
    calc
      (actualXiCriticalReadout t : ℂ) =
          ((hardyNormalizationFactor t * candidateHardyZ t : ℝ) : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) hfactor
      _ = ((-hardyNormalizationFactor t : ℝ) : ℂ) *
          ((-candidateHardyZ t : ℝ) : ℂ) := by
        push_cast
        ring

@[simp] theorem candidateHardyZDatum_Z (t : ℝ) :
    candidateHardyZDatum.Z t = -candidateHardyZ t := rfl

@[simp] theorem candidateHardyZDatum_xi_crit (t : ℝ) :
    candidateHardyZDatum.xi_crit t = (actualXiCriticalReadout t : ℂ) := rfl

theorem candidateHardyZDatum_zero_iff_xi_zero (t : ℝ) :
    candidateHardyZDatum.Z t = 0 ↔
      candidateHardyZDatum.xi_crit t = 0 := by
  rw [candidateHardyZDatum_Z, candidateHardyZDatum_xi_crit]
  simpa using (actualXiCriticalReadout_zero_iff_candidateHardyZ_zero t).symm

end InfoGeometry.Canonical.CandidateHardyZDatumBridge
