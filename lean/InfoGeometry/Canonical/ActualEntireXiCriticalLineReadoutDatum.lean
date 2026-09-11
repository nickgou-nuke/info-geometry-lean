import InfoGeometry.Topology.ActualXiHardyZRealizationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge
import InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge
import InfoGeometry.Canonical.ActualEntireXiReadoutNormalizationBridge

/-!
# Actual entire-Xi critical-line readout datum

This module realizes the generic `ConcreteHardyZDatum` interface using the
actual pole-removed completed Riemann function and its real critical-line
readout.  The factor is the trivial unit factor `r = 1`.

This is deliberately not a claim that the readout is the classical
Riemann--Siegel Hardy `Z` function: no Riemann--Siegel theta phase is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireXiCriticalLineReadoutDatum

open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge
open InfoGeometry.Topology.ActualXiHardyZRealization
open InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.ActualEntireXiReadoutNormalizationBridge

/-- The actual real critical-line readout, with its exact complex source. -/
def actualEntireXiCriticalLineReadoutDatum : ConcreteHardyZDatum where
  Z := criticalLineRealReadout entireRiemannXi
  r := fun _ => 1
  r_ne_zero := by
    intro t
    norm_num
  Xi_eval := fun t => entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
  Xi_eq_r_mul_Z := by
    intro t
    have hread :=
      criticalLineRealReadout_eq_xi entireRiemannXi
        actualEntireRiemannXiFunctionDatum t
    simpa using hread.symm

@[simp] theorem actualEntireXiCriticalLineReadoutDatum_Z (t : ℝ) :
    actualEntireXiCriticalLineReadoutDatum.Z t =
      criticalLineRealReadout entireRiemannXi t := rfl

@[simp] theorem actualEntireXiCriticalLineReadoutDatum_Xi_eval (t : ℝ) :
    actualEntireXiCriticalLineReadoutDatum.Xi_eval t =
      entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := rfl

theorem actualEntireXiCriticalLineReadoutDatum_Z_eq_normalization_Z
    (t : ℝ) :
    actualEntireXiCriticalLineReadoutDatum.Z t =
      actualEntireRiemannXiReadoutNormalizationDatum.Z t := rfl

theorem actualEntireXiCriticalLineReadoutDatum_Xi_eval_eq_normalization_xi_crit
    (t : ℝ) :
    actualEntireXiCriticalLineReadoutDatum.Xi_eval t =
      (actualEntireRiemannXiReadoutNormalizationDatum.xi_crit t : ℂ) := by
  change entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) =
    (criticalLineRealReadout entireRiemannXi t : ℂ)
  exact (criticalLineRealReadout_eq_xi entireRiemannXi
    actualEntireRiemannXiFunctionDatum t).symm

theorem actualEntireXiCriticalLineReadoutDatum_zero_iff (t : ℝ) :
    actualEntireXiCriticalLineReadoutDatum.Z t = 0 ↔
      entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0 := by
  change criticalLineRealReadout entireRiemannXi t = 0 ↔
    entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0
  exact (hardy_z_zero_equivalence actualEntireXiCriticalLineReadoutDatum t).symm

theorem actualEntireXiCriticalLineReadoutDatum_zero_iff_riemannXi_zero
    (t : ℝ) :
    actualEntireXiCriticalLineReadoutDatum.Z t = 0 ↔
      riemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0 := by
  rw [actualEntireXiCriticalLineReadoutDatum_zero_iff]
  have hs0 : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
  have hs1 : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
  rw [entireRiemannXi_eq_riemannXi hs0 hs1]

end InfoGeometry.Canonical.ActualEntireXiCriticalLineReadoutDatum
