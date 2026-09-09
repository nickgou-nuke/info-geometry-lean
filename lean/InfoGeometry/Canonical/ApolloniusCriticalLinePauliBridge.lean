import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Canonical.HestenesPauliSheetBridge

/-!
# Apollonius critical-line / circular Pauli bridge

This file records the elementary, theorem-honest bridge between the marked
pair `0, 1` and the circular Pauli ladder.  It makes no claim about zeta
zeros or the Riemann hypothesis.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusCriticalLinePauliBridge

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Canonical.HestenesPauliSheetBridge

def distSqZero (s : ℂ) : ℝ := s.re ^ 2 + s.im ^ 2

def distSqOne (s : ℂ) : ℝ := (s.re - 1) ^ 2 + s.im ^ 2

def apolloniusBalance (s : ℂ) : ℝ := distSqZero s - distSqOne s

theorem apolloniusBalance_eq_two_re_sub_one (s : ℂ) :
    apolloniusBalance s = 2 * s.re - 1 := by
  unfold apolloniusBalance distSqZero distSqOne
  ring

theorem equidistant_zero_one_iff_criticalLine (s : ℂ) :
    distSqZero s = distSqOne s ↔ CriticalLine s := by
  rw [criticalLine_iff_re_eq_half]
  unfold distSqZero distSqOne
  constructor <;> intro h <;> nlinarith

theorem apolloniusBalance_eq_zero_iff_criticalLine (s : ℂ) :
    apolloniusBalance s = 0 ↔ CriticalLine s := by
  rw [apolloniusBalance_eq_two_re_sub_one, criticalLine_iff_re_eq_half]
  constructor <;> intro h <;> linarith

def apolloniusRatioSq (s : ℂ) : ℝ := distSqZero s / distSqOne s

theorem distSqOne_pos_of_criticalLine {s : ℂ} (hs : CriticalLine s) :
    0 < distSqOne s := by
  rw [criticalLine_iff_re_eq_half] at hs
  unfold distSqOne
  rw [hs]
  have him : 0 ≤ s.im ^ 2 := sq_nonneg s.im
  nlinarith

theorem apolloniusRatioSq_eq_one_of_criticalLine {s : ℂ}
    (hs : CriticalLine s) : apolloniusRatioSq s = 1 := by
  have heq : distSqZero s = distSqOne s :=
    (equidistant_zero_one_iff_criticalLine s).2 hs
  have hne : distSqOne s ≠ 0 := ne_of_gt (distSqOne_pos_of_criticalLine hs)
  unfold apolloniusRatioSq
  rw [heq]
  exact div_self hne

def apolloniusLogPotential (s : ℂ) : ℝ := Real.log (apolloniusRatioSq s)

theorem apolloniusLogPotential_eq_zero_of_criticalLine {s : ℂ}
    (hs : CriticalLine s) : apolloniusLogPotential s = 0 := by
  unfold apolloniusLogPotential
  rw [apolloniusRatioSq_eq_one_of_criticalLine hs]
  exact Real.log_one

def matrixCommutator (A B : M2C) : M2C := A * B - B * A

theorem circular_commutator :
    matrixCommutator circularPlus circularMinus = hestenesParity := by
  unfold matrixCommutator
  rw [circularPlus_mul_circularMinus, circularMinus_mul_circularPlus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesScalar, hestenesParity,
      InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetIdentity,
      InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetParity,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply] <;> ring

theorem parity_circularPlus_commutator :
    matrixCommutator hestenesParity circularPlus = (2 : ℂ) • circularPlus := by
  rw [circularPlus_eq_sigmaPlus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, hestenesParity,
      InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetParity,
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sigmaPlus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

theorem parity_circularMinus_commutator :
    matrixCommutator hestenesParity circularMinus = (-2 : ℂ) • circularMinus := by
  rw [circularMinus_eq_sigmaMinus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, hestenesParity,
      InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetParity,
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sigmaMinus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

theorem apollonius_pauli_exact_packet (s : ℂ) :
    (distSqZero s = distSqOne s ↔ CriticalLine s) ∧
    matrixCommutator circularPlus circularMinus = hestenesParity ∧
    circularPlus * circularMinus + circularMinus * circularPlus = hestenesScalar := by
  exact ⟨equidistant_zero_one_iff_criticalLine s,
    circular_commutator, circular_anticommutator⟩

end InfoGeometry.Canonical.ApolloniusCriticalLinePauliBridge
