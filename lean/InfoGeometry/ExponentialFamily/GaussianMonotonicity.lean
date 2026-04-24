import InfoGeometry.ExponentialFamily.Gaussian
import Mathlib.Analysis.InnerProductSpace.Basic

open InfoGeometry.ExponentialFamily.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The gradient map of the Gaussian log-partition function is monotone:
  0 ≤ ⟪G.sigma η₁ - G.sigma η₂, η₁ - η₂⟫
This follows from the positive-definiteness of the covariance operator.
-/
lemma gaussian_grad_monotone (G : GaussianFamily E) (η₁ η₂ : E) :
  0 ≤ inner ℝ (G.sigma η₁ - G.sigma η₂) (η₁ - η₂) :=
by
  by_cases h : η₁ = η₂
  · subst η₁
    simp
  · have hdiff : η₁ - η₂ ≠ 0 := sub_ne_zero.mpr h
    have hsigma : G.sigma η₁ - G.sigma η₂ = G.sigma (η₁ - η₂) := by
      simp
    rw [hsigma]
    rw [real_inner_comm]
    exact le_of_lt (G.sigma_pos (η₁ - η₂) hdiff)
