import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Canonical.ActualEntireCenteredXiBridge
import InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
import InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge

/-!
# Critical-line coherence of the two actual completed-xi readouts

The pole-removed entire representative and Mathlib's regular `riemannXi`
agree on the critical line.  This owner exposes that equality in centered
coordinates and transports it to the real-part readout used by the existing
symmetry datum.  No Hardy-Z identification or zero-location statement is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireCenteredXiRegularityInterop

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireCenteredXiBridge
open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
open InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
open InfoGeometry.Canonical.XiHardyZNormalization
open InfoGeometry.Topology.XiHardyZNormalizationBridge

theorem criticalLinePoint_ne_zero (t : ℝ) :
    (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have hRe := congrArg Complex.re h
  norm_num at hRe

theorem criticalLinePoint_ne_one (t : ℝ) :
    (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
  intro h
  have hRe := congrArg Complex.re h
  norm_num at hRe

theorem actualEntireCenteredXi_criticalLine_eq_centeredRiemannXi (t : ℝ) :
    actualEntireCenteredXi (Complex.I * (t : ℂ)) =
      centeredRiemannXi 0 t := by
  unfold actualEntireCenteredXi centeredRiemannXi
  rw [entireRiemannXi_eq_riemannXi
    (criticalLinePoint_ne_zero t) (criticalLinePoint_ne_one t)]
  norm_num

theorem actualEntireCenteredXi_criticalLine_re_eq (t : ℝ) :
    (actualEntireCenteredXi (Complex.I * (t : ℂ))).re =
      centeredRiemannXiReal 0 t := by
  exact congrArg Complex.re
    (actualEntireCenteredXi_criticalLine_eq_centeredRiemannXi t)

theorem actualEntireCenteredXi_criticalLine_eq_realReadout (t : ℝ) :
    actualEntireCenteredXi (Complex.I * (t : ℂ)) =
      (centeredRiemannXiReal 0 t : ℂ) := by
  calc
    actualEntireCenteredXi (Complex.I * (t : ℂ)) =
        centeredRiemannXi 0 t :=
      actualEntireCenteredXi_criticalLine_eq_centeredRiemannXi t
    _ = (centeredRiemannXiReal 0 t : ℂ) :=
      actualXiSymmetryDatum_concrete_criticalLine_real t

theorem actualEntireCenteredXi_criticalLine_eq_candidate_factor (t : ℝ) :
    actualEntireCenteredXi (Complex.I * (t : ℂ)) =
      (hardyNormalizationFactor t * candidateHardyZ t : ℂ) := by
  rw [actualEntireCenteredXi_criticalLine_eq_realReadout]
  exact_mod_cast actualXiCriticalReadout_eq_factor_mul_candidateHardyZ t

theorem actualEntireCenteredXi_criticalLine_zero_iff_candidateHardyZ_zero
    (t : ℝ) :
    actualEntireCenteredXi (Complex.I * (t : ℂ)) = 0 ↔
      candidateHardyZ t = 0 := by
  rw [actualEntireCenteredXi_criticalLine_eq_candidate_factor]
  norm_cast
  exact zero_iff_of_mul_eq_zero_of_ne_zero _ _
    (hardyNormalizationFactor_ne_zero t)

end InfoGeometry.Canonical.ActualEntireCenteredXiRegularityInterop
