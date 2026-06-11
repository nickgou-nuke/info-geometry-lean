import Mathlib
import InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

theorem test_dirichlet_mode_factorization (n : ℝ) (hn : 0 < n) (x : CenteredChart) :
    (n : ℂ) ^ (-(centeredParameter x)) =
      centeredDirichletMode (Real.log n) x := by
  sorry
