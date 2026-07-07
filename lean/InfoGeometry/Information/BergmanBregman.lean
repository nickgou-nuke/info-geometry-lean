import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Convex.Bregman

namespace InfoGeometry.Information

/-- A simple information-theoretic localization packet built from a one-dimensional
Bregman divergence and a pointwise residual. -/
def bergmanLocalization (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  InfoGeometry.bregmanDiv F x y

/-- The localization packet vanishes on the diagonal. -/
theorem bergmanLocalization_self (F : ℝ → ℝ) (x : ℝ) :
    bergmanLocalization F x x = 0 := by
  simpa [bergmanLocalization] using InfoGeometry.bregmanDiv_self F x

/-- If the derivatives match, the localization packet obeys the three-point law. -/
theorem bergmanLocalization_threePoint_eq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hderiv : deriv F y = deriv F z) :
    bergmanLocalization F x z = bergmanLocalization F x y + bergmanLocalization F y z := by
  simpa [bergmanLocalization] using InfoGeometry.bregmanThreePoint_eq_of_deriv_eq F x y z hderiv

end InfoGeometry.Information
