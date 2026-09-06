import InfoGeometry.Canonical.XiHardyZNormalizationBridge
import InfoGeometry.Topology.ActualEntireXiRealReadoutBridge

/-!
# Canonical normalization of the actual entire-Xi critical-line readout

This file transports the already constructed real readout of `entireRiemannXi`
into the canonical `HardyZNormalizationDatum` interface.  The normalization
factor is the unit factor, so this is not a construction of the classical
Hardy `Z` function or of a Riemann--Siegel phase.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireXiReadoutNormalizationBridge

open InfoGeometry.Canonical.XiHardyZNormalization
open InfoGeometry.Topology.ActualEntireXiRealReadoutBridge
open InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge
open InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge

def actualEntireRiemannXiReadoutNormalizationDatum :
    HardyZNormalizationDatum where
  xi_crit := criticalLineRealReadout entireRiemannXi
  Z := criticalLineRealReadout entireRiemannXi
  r := fun _ => 1
  r_ne_zero := by
    intro t
    norm_num
  rel := by
    intro t
    simp

@[simp] theorem actualEntireRiemannXiReadoutNormalizationDatum_xi_crit
    (t : ℝ) :
    actualEntireRiemannXiReadoutNormalizationDatum.xi_crit t =
      criticalLineRealReadout entireRiemannXi t := rfl

@[simp] theorem actualEntireRiemannXiReadoutNormalizationDatum_Z
    (t : ℝ) :
    actualEntireRiemannXiReadoutNormalizationDatum.Z t =
      criticalLineRealReadout entireRiemannXi t := rfl

theorem actualEntireRiemannXiReadoutNormalizationDatum_even (t : ℝ) :
    actualEntireRiemannXiReadoutNormalizationDatum.Z (-t) =
      actualEntireRiemannXiReadoutNormalizationDatum.Z t := by
  simpa only [actualEntireRiemannXiReadoutNormalizationDatum_Z] using
    InfoGeometry.Topology.ActualEntireXiRealReadoutBridge.actualEntireRiemannXiRealReadout_even t

theorem actualEntireRiemannXiReadoutNormalizationDatum_zero_iff (t : ℝ) :
    actualEntireRiemannXiReadoutNormalizationDatum.xi_crit t = 0 ↔
      actualEntireRiemannXiReadoutNormalizationDatum.Z t = 0 := by
  exact xi_crit_zero_iff_Z_zero actualEntireRiemannXiReadoutNormalizationDatum t

theorem actualEntireRiemannXiReadoutNormalizationDatum_zero_iff_riemannXi_zero
    (t : ℝ) :
    actualEntireRiemannXiReadoutNormalizationDatum.Z t = 0 ↔
      riemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0 := by
  change criticalLineRealReadout entireRiemannXi t = 0 ↔ _
  rw [criticalLineRealReadout_zero_iff_xi_zero entireRiemannXi
    actualEntireRiemannXiFunctionDatum t]
  have hs0 : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
  have hs1 : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
  rw [entireRiemannXi_eq_riemannXi hs0 hs1]

end InfoGeometry.Canonical.ActualEntireXiReadoutNormalizationBridge
