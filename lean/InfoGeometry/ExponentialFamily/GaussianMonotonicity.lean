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
  have : G.sigma η₁ - G.sigma η₂ = G.sigma (η₁ - η₂) := by simp [LinearMap.map_sub]
  rw [this]
  exact G.sigma_pos (η₁ - η₂) (sub_ne_zero_of_ne (ne_of_apply_ne (fun x => x) (ne_of_ne (η₁ ≠ η₂))))
