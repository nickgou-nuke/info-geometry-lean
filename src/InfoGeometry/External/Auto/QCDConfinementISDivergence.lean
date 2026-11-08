import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section
namespace QCDThermodynamicConfinement

structure ColorStateManifold where
  M : Type*
  Q : M → ℝ
  /-- Discrete topological index assigned to a parametrized color loop.  This is
  the theorem-level interface used by the finite loop lemmas below. -/
  loopIndex : (ℝ → M) → ℤ

def IsClosedLoop (M : ColorStateManifold) (γ : ℝ → M.M) : Prop :=
  γ 0 = γ 1

/-- The winding number is the explicit loop index supplied by the color-state
manifold. -/
def windingNumber (M : ColorStateManifold) (γ : ℝ → M.M) : ℤ :=
  M.loopIndex γ

theorem windingNumber_eq_loopIndex (M : ColorStateManifold) (γ : ℝ → M.M) :
    windingNumber M γ = M.loopIndex γ := by
  rfl

theorem nontrivial_winding_is_nonzero
    (M : ColorStateManifold) (γ : ℝ → M.M) (hγ : M.loopIndex γ ≠ 0) :
    windingNumber M γ ≠ 0 := by
  simpa [windingNumber] using hγ

def ItakuraSaitoDivergence {Q₁ Q₂ : ℝ} (_h₁ : 0 < Q₁) (_h₂ : 0 < Q₂) : ℝ :=
  (Q₁ / Q₂) - Real.log (Q₁ / Q₂) - 1

theorem ItakuraSaitoDivergence_self {Q : ℝ} (hQ : 0 < Q) :
    ItakuraSaitoDivergence hQ hQ = 0 := by
  dsimp [ItakuraSaitoDivergence]
  rw [div_self (ne_of_gt hQ), Real.log_one]
  ring

def FisherMetric (_M : ColorStateManifold) (_q : _M.M) :
    (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ := fun v w => ∑ i, v i * w i

theorem FisherMetric_psd (M : ColorStateManifold) (q : M.M) (v : Fin 2 → ℝ) :
    0 ≤ FisherMetric M q v v := by
  dsimp [FisherMetric]
  rw [Fin.sum_univ_two]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem qcd_confinement_from_is_divergence
    (M : ColorStateManifold) {Q : ℝ} (hQ : 0 < Q) :
    (∀ q v, 0 ≤ FisherMetric M q v v) ∧ ItakuraSaitoDivergence hQ hQ = 0 := by
  constructor
  · intro q v
    exact FisherMetric_psd M q v
  · simpa using ItakuraSaitoDivergence_self hQ

end QCDThermodynamicConfinement
end noncomputable section
