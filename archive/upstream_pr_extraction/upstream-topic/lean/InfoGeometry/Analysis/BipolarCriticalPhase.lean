import InfoGeometry.Analysis.BipolarCrossRatioLog
import Mathlib.Tactic

/-!
# Branch-independent critical-line phase

The principal-log formula involving `2 * atan (2y)` is secondary and branch
sensitive.  The canonical global statement on the vertical bisector is the
rational Cayley phase

`q(1/2 + i y) = (1 + 2 i y) / (1 - 2 i y)`.

This file records that identity and its unit-modulus consequence without any
choice of argument branch.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarCriticalPhase

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- Rational unit-circle phase attached to the critical-line coordinate `y`. -/
def criticalPhase (y : ℝ) : ℂ :=
  ((1 : ℂ) + (2 * y : ℝ) * Complex.I) /
    ((1 : ℂ) - (2 * y : ℝ) * Complex.I)

lemma criticalPhase_den_ne_zero (y : ℝ) :
    (1 : ℂ) - (2 * y : ℝ) * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

/-- Exact branch-independent phase formula on the vertical bisector. -/
theorem crossRatio01_criticalLine_eq_criticalPhase (y : ℝ) :
    crossRatio01 (criticalLine y) = criticalPhase y := by
  unfold crossRatio01 cayleyToFugacity criticalLine criticalPhase
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hden : ((1 / 2 : ℝ) : ℂ) - (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  field_simp [h2, hden, criticalPhase_den_ne_zero y]
  ring

/-- The rational critical phase has unit norm. -/
theorem norm_criticalPhase (y : ℝ) : ‖criticalPhase y‖ = 1 := by
  rw [← crossRatio01_criticalLine_eq_criticalPhase]
  exact norm_crossRatio01_criticalLine y

/-- The rational phase is inverse to its complex conjugate. -/
theorem criticalPhase_mul_conj (y : ℝ) :
    criticalPhase y * Complex.conj (criticalPhase y) = 1 := by
  have hnorm := norm_criticalPhase y
  have hsq : Complex.normSq (criticalPhase y) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  simpa [Complex.normSq_apply, mul_comm] using hsq

/-- Critical phase at the midpoint is the identity. -/
@[simp] theorem criticalPhase_zero : criticalPhase 0 = 1 := by
  simp [criticalPhase]

end InfoGeometry.Analysis.BipolarCriticalPhase
