import InfoGeometry.External.Auto.ModularHolographicMetric
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite RG fixed-point metric identities

This module records the real `2×2` Pauli boost calculation and links it to the
active complex `ModularHolographicMetric` calculation.  Both statements are
local scalar-square identities, not global renormalization-group theorems.
-/

noncomputable section

namespace RGFixedPoint

open Matrix

abbrev Mat2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Real Pauli boost generator. -/
def K_boost (v : ℝ) : Mat2R := !![0, v; v, 0]

/-- The finite boost square gives the scalar quadratic metric term. -/
theorem bures_metric_closure (v : ℝ) :
    K_boost v * K_boost v = v ^ 2 • (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [K_boost, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, pow_two]

/-- Complex active-module version of the same scalar-square identity. -/
theorem modular_holographic_metric_bridge (v : ℂ) :
    ModularHolographicMetric.Kboost v * ModularHolographicMetric.Kboost v =
      (v * v) • (1 : ModularHolographicMetric.M2C) := by
  exact ModularHolographicMetric.Kboost_sq_scalar v

end RGFixedPoint
