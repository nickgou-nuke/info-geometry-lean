import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open Real

/-- 
The β-divergence energy geometry.
This module defines the three canonical variance limits.

β=2: Gaussian additive-noise energy. 
-/
noncomputable def betaDivergenceGaussian (x b : ℝ) : ℝ :=
  (1 / 2) * (x - b)^2

/-- β=1: Poisson count likelihood energy (Kullback-Leibler). -/
noncomputable def betaDivergencePoisson (x b : ℝ) : ℝ :=
  x * Real.log (x / b) - x + b

/-- β=0: Gamma/multiplicative Itakura-Saito energy. -/
noncomputable def betaDivergenceGamma (x b : ℝ) : ℝ :=
  (x / b) - Real.log (x / b) - 1

/-- Gaussian divergence is non-negative. -/
theorem betaDivergenceGaussian_nonneg (x b : ℝ) :
    0 ≤ betaDivergenceGaussian x b := by
  dsimp [betaDivergenceGaussian]
  have h : 0 ≤ (x - b)^2 := sq_nonneg (x - b)
  exact mul_nonneg (by norm_num) h

/-- Gaussian divergence is zero when x = b. -/
theorem betaDivergenceGaussian_self (b : ℝ) :
    betaDivergenceGaussian b b = 0 := by
  dsimp [betaDivergenceGaussian]
  ring

end InfoGeometry.Canonical
