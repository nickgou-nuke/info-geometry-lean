import Mathlib
import InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

theorem dirichlet_mode_factorization (n : ℝ) (hn : 0 < n) (x : CenteredChart) :
    (n : ℂ) ^ (-(centeredParameter x)) =
      centeredDirichletMode (Real.log n) x := by
  sorry

