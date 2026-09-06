import InfoGeometry.Canonical.CandidateHardyZDatumBridge
import InfoGeometry.Canonical.RiemannSiegelThetaParityBridge

/-!
# Candidate Riemann--Siegel datum from the native completed-Xi readout

This file supplies the finite `RiemannSiegelDatum` interface using the
repository's explicit `candidateHardyZ`.  The phase is the trivial candidate
phase, so this is not an identification with the classical Riemann--Siegel
theta function or Hardy `Z` function.
-/

noncomputable section

namespace InfoGeometry.Canonical.CandidateRiemannSiegelDatumBridge

open InfoGeometry.Canonical.CandidateHardyZDatumBridge
open InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
open InfoGeometry.Canonical.RiemannSiegelThetaParity

def candidateRiemannSiegelDatum : RiemannSiegelDatum where
  Z := fun t => -candidateHardyZ t
  theta := fun _ => 0
  cos_theta := fun _ => 1
  sin_theta := fun _ => 0
  Z_even := by
    intro t
    simp [candidateHardyZ_neg]
  theta_odd := by
    intro t
    simp
  cos_even_rel := by
    intro t
    simp
  sin_odd_rel := by
    intro t
    simp
  pythagoras := by
    intro t
    norm_num

@[simp] theorem candidateRiemannSiegelDatum_Z (t : ℝ) :
    candidateRiemannSiegelDatum.Z t = -candidateHardyZ t := rfl

@[simp] theorem candidateRiemannSiegelDatum_zetaCrit (t : ℝ) :
    zetaCrit candidateRiemannSiegelDatum t =
      (-(candidateHardyZ t) : ℂ) := by
  apply Complex.ext <;> simp [zetaCrit, candidateRiemannSiegelDatum]

theorem candidateRiemannSiegelDatum_zero_iff (t : ℝ) :
    zetaCrit candidateRiemannSiegelDatum t = 0 ↔
      candidateRiemannSiegelDatum.Z t = 0 := by
  exact zetaCrit_zero_iff_Z_zero candidateRiemannSiegelDatum t

end InfoGeometry.Canonical.CandidateRiemannSiegelDatumBridge
