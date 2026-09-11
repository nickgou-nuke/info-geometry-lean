import InfoGeometry.Canonical.PowerVarianceCumulants
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact third-order cumulant boundary

These are finite algebraic consequences of the already-defined model
cumulants.  They are deliberately not named Chentsov tensors: no statistical
manifold, tensor bundle, or uniqueness theorem is asserted here.
-/

namespace InfoGeometry.Canonical

theorem gaussianCumulant_three (μ : ℝ) :
    gaussianCumulant μ 3 = 0 := by
  rfl

theorem poissonCumulant_three (μ : ℝ) :
    poissonCumulant μ 3 = μ := by
  exact poissonCumulant_eq μ (by norm_num)

theorem gammaCumulant_three (μ : ℝ) :
    gammaCumulant μ 3 = 2 * μ ^ 3 := by
  rw [gammaCumulant_eq_factorial_mul_pow μ (by norm_num)]
  norm_num

end InfoGeometry.Canonical
