import InfoGeometry.Physics.Thermodynamics.ChiralSimilarityWeightedSelfAdjointness
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics.Thermodynamics

open InfoGeometry.Physics
open Matrix

noncomputable section

/-!
# Positive weighted self-adjointness

The diagonal operator below is a positive weight.  It is not a Krein
fundamental symmetry: no involution or indefinite form is asserted here.
-/

/-- The positive diagonal weight `ημ = diag (exp (-2 μ), exp (2 μ))`. -/
noncomputable def etaMetric (μ : ℝ) : BdGBlock ℝ :=
  chiralKreinMetric μ

/-- Matrix weighted self-adjointness, written with the real transpose. -/
def IsWeightedSelfAdjoint
    (η D : BdGBlock ℝ) : Prop :=
  D.transpose * η = η * D

@[simp] theorem etaMetric_eq_chiralKreinMetric (μ : ℝ) :
    etaMetric μ = chiralKreinMetric μ :=
  rfl

@[simp] theorem etaMetric_entries (μ : ℝ) :
    etaMetric μ 0 0 = Real.exp (-2 * μ) ∧
    etaMetric μ 1 1 = Real.exp (2 * μ) ∧
    etaMetric μ 0 1 = 0 ∧
    etaMetric μ 1 0 = 0 := by
  simp [etaMetric, chiralKreinMetric, gibbsFactor]

theorem etaMetric_diagonal_entries_pos (μ : ℝ) :
    0 < etaMetric μ 0 0 ∧ 0 < etaMetric μ 1 1 := by
  have h := etaMetric_entries μ
  constructor
  · rw [h.1]
    exact Real.exp_pos _
  · rw [h.2.1]
    exact Real.exp_pos _

@[simp] theorem deformedDirac_weighted_self_adjoint
    (μ Δ : ℝ) :
    IsWeightedSelfAdjoint
      (etaMetric μ)
      (chemicalPotentialDiracFlow μ Δ) := by
  unfold IsWeightedSelfAdjoint
  simpa [etaMetric, Matrix.star_eq_conjTranspose] using
    (chemicalPotentialDiracFlow_weighted_selfAdjoint μ Δ)

end

end InfoGeometry.Physics.Thermodynamics
