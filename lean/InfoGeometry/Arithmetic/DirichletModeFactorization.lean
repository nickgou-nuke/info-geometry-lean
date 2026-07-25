import Mathlib.Tactic
import InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

theorem test_dirichlet_mode_factorization (n : ℝ) (hn : 0 < n) (x : CenteredChart) :
    (n : ℂ) ^ (-(centeredParameter x)) =
      centeredDirichletMode (Real.log n) x := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hn0]
  rw [← Complex.ofReal_log (le_of_lt hn)]
  rw [centeredDirichletMode, criticalLineWeight, scaleEnvelope, phaseWave]
  rw [centeredParameter_eq_half_plus_u_plus_iv]
  simp only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring
