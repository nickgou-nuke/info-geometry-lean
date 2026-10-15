import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ViazovskaMagicFunctionBridge

open ViazovskaMagicFunctionBridge

noncomputable section

namespace InfoGeometry.Canonical.ViazovskaCohnElkiesMellin

/-!
# Viazovska Magic Function & Cohn-Elkies Linear Programming Bound

This module contains a scalar-data carrier for a Cohn--Elkies-style bound,
its elementary nonnegativity consequence, and a stipulated E₈ density value.
It does not construct Viazovska's analytic magic function or prove its Fourier
transform properties from an explicit function.  Bost--Connes partition sums
and prime-product identities are a separate arithmetic development; this
module proves no Mellin-transform or KMS connection.
-/

/-- Scalar ratio used in density-bound formulas.  No packing or Fourier data is
bundled into this arithmetic definition. -/
def positiveDensityRatio (vol_ball f_fourier_zero f_zero : ℝ) : ℝ :=
  vol_ball * (f_fourier_zero / f_zero)

/-- Nonnegativity of the scalar ratio when its volume and numerator are
nonnegative and its denominator is positive. -/
theorem positiveDensityRatio_nonneg
    (vol_ball f_fourier_zero f_zero : ℝ)
    (hvol : 0 ≤ vol_ball) (hnum : 0 ≤ f_fourier_zero) (hden : 0 < f_zero) :
    0 ≤ positiveDensityRatio vol_ball f_fourier_zero f_zero := by
  dsimp [positiveDensityRatio]
  exact mul_nonneg hvol (div_nonneg hnum (le_of_lt hden))

/-- The scalar `π⁴ / 384` associated with the E₈ sphere-packing density. -/
def viazovskaE8Density : ℝ := (Real.pi ^ 4) / 384

/-- **Theorem**: Viazovska's E₈ density constant is strictly positive. -/
theorem viazovskaE8Density_pos : 0 < viazovskaE8Density := by
  dsimp [viazovskaE8Density]
  have hpi4 : 0 < Real.pi ^ 4 := by positivity
  exact div_pos hpi4 (by norm_num)

end InfoGeometry.Canonical.ViazovskaCohnElkiesMellin
