import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

noncomputable section
namespace InfoGeometry.Analysis.BipolarCriticalPhase

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

def criticalPhase (y : ℝ) : ℂ :=
  ((1 : ℂ) + (2 * y : ℝ) * Complex.I) /
    ((1 : ℂ) - (2 * y : ℝ) * Complex.I)

lemma criticalPhase_den_ne_zero (y : ℝ) :
    (1 : ℂ) - (2 * y : ℝ) * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem crossRatio01_criticalLine_eq_criticalPhase (y : ℝ) :
    crossRatio01 (criticalLine y) = criticalPhase y := by
  unfold crossRatio01 cayleyToFugacity criticalLine criticalPhase
  have hden : ((1 / 2 : ℝ) : ℂ) - (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  norm_num
  field_simp [hden, criticalPhase_den_ne_zero y]
  push_cast
  ring

theorem norm_criticalPhase (y : ℝ) : ‖criticalPhase y‖ = 1 := by
  rw [← crossRatio01_criticalLine_eq_criticalPhase]
  exact norm_crossRatio01_criticalLine y

theorem criticalPhase_mul_conj (y : ℝ) :
    criticalPhase y * (starRingEnd ℂ) (criticalPhase y) = 1 := by
  calc
    criticalPhase y * (starRingEnd ℂ) (criticalPhase y) =
        Complex.normSq (criticalPhase y) := by
      simpa [Complex.star_def] using Complex.mul_conj (criticalPhase y)
    _ = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_criticalPhase y]
      norm_num

@[simp] theorem criticalPhase_zero : criticalPhase 0 = 1 := by
  simp [criticalPhase]

end InfoGeometry.Analysis.BipolarCriticalPhase
