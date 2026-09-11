import InfoGeometry.ExponentialFamily.Gaussian
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic

namespace InfoGeometry.ExponentialFamily

open InfoGeometry.ExponentialFamily.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The gradient map of the Gaussian log-partition function is monotone:
  0 ≤ ⟪G.sigma η₁ - G.sigma η₂, η₁ - η₂⟫
This follows from the positive-definiteness of the covariance operator.
-/
lemma gaussian_grad_monotone (G : GaussianFamily E) (η₁ η₂ : E) :
  0 ≤ inner ℝ (G.sigma η₁ - G.sigma η₂) (η₁ - η₂) := by
  have hsub : G.sigma η₁ - G.sigma η₂ = G.sigma (η₁ - η₂) := by
    simp
  rw [hsub]
  by_cases hzero : η₁ - η₂ = 0
  · simp [hzero]
  · simpa [real_inner_comm] using (le_of_lt (G.sigma_pos (η₁ - η₂) hzero))

end InfoGeometry.ExponentialFamily
