import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

noncomputable section

def loxodromicScalarInvariant (η θ : ℝ) : ℝ :=
  η ^ 2 - θ ^ 2

def loxodromicPseudoscalarInvariant (η θ : ℝ) : ℝ :=
  2 * η * θ

def loxodromicNormSquare (η θ : ℝ) : ℝ :=
  η ^ 2 + θ ^ 2

theorem loxodromic_invariant_pythagorean (η θ : ℝ) :
    loxodromicScalarInvariant η θ ^ 2 +
        loxodromicPseudoscalarInvariant η θ ^ 2 =
      loxodromicNormSquare η θ ^ 2 := by
  simp only [loxodromicScalarInvariant, loxodromicPseudoscalarInvariant,
    loxodromicNormSquare]
  ring

theorem loxodromicNormSquare_nonneg (η θ : ℝ) :
    0 ≤ loxodromicNormSquare η θ := by
  simp only [loxodromicNormSquare]
  positivity

theorem loxodromic_recover_eta_square (η θ : ℝ) :
    (loxodromicNormSquare η θ + loxodromicScalarInvariant η θ) / 2 = η ^ 2 := by
  simp only [loxodromicNormSquare, loxodromicScalarInvariant]
  ring

theorem loxodromic_recover_theta_square (η θ : ℝ) :
    (loxodromicNormSquare η θ - loxodromicScalarInvariant η θ) / 2 = θ ^ 2 := by
  simp only [loxodromicNormSquare, loxodromicScalarInvariant]
  ring

end

end InfoGeometry.Canonical
