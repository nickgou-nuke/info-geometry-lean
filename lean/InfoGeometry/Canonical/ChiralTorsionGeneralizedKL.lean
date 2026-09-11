import InfoGeometry.Canonical.GeneralizedKL
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChiralTorsionBridge

section GeneralizedKL

variable {α : Type*} [Fintype α]

/-- Gibbs regularizer induced by generalized (unnormalized) KL energy. -/
noncomputable def gibbsSmoothingOnGeneralizedKL
    (β : ℝ) (μ ν μ₀ : α → ℝ) : ℝ :=
  Real.exp (-β * generalizedKL μ ν μ₀)

/-- Lemma `gibbsSmoothingOnGeneralizedKL_pos`. -/
lemma gibbsSmoothingOnGeneralizedKL_pos
    (β : ℝ) (μ ν μ₀ : α → ℝ) :
    0 < gibbsSmoothingOnGeneralizedKL β μ ν μ₀ := by
  unfold gibbsSmoothingOnGeneralizedKL
  exact Real.exp_pos _

/-- Lemma `gibbsSmoothingOnGeneralizedKL_nonneg`. -/
lemma gibbsSmoothingOnGeneralizedKL_nonneg
    (β : ℝ) (μ ν μ₀ : α → ℝ) :
    0 ≤ gibbsSmoothingOnGeneralizedKL β μ ν μ₀ := by
  exact (gibbsSmoothingOnGeneralizedKL_pos β μ ν μ₀).le

end GeneralizedKL

end InfoGeometry.Canonical.ChiralTorsionBridge
