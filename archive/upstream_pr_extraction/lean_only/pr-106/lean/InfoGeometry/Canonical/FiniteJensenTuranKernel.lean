import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-!
# Finite Jensen--Turán algebra

This owner contains the degree-two coefficient kernel behind the first Turán
inequality.  It does not assert that a zeta or Xi function satisfies any of
these inequalities, and it does not encode a real-rootedness theorem.
-/

namespace InfoGeometry.Canonical.FiniteJensenTuranKernel

noncomputable section

open Polynomial

/-- The first finite Turán expression for three consecutive coefficients. -/
def turan (a₀ a₁ a₂ : ℝ) : ℝ := a₁ ^ 2 - a₀ * a₂

/-- The degree-two Jensen polynomial with coefficient data `a₀,a₁,a₂`. -/
def jensenQuadratic (a₀ a₁ a₂ : ℝ) : Polynomial ℝ :=
  C a₀ + C (2 * a₁) * X + C a₂ * X ^ 2

theorem jensenQuadratic_eval
    (a₀ a₁ a₂ x : ℝ) :
    (jensenQuadratic a₀ a₁ a₂).eval x =
      a₀ + 2 * a₁ * x + a₂ * x ^ 2 := by
  simp [jensenQuadratic]

/-- The ordinary quadratic discriminant of the degree-two Jensen kernel. -/
def quadraticDiscriminant (a₀ a₁ a₂ : ℝ) : ℝ :=
  (2 * a₁) ^ 2 - 4 * a₂ * a₀

theorem quadraticDiscriminant_eq_four_turan
    (a₀ a₁ a₂ : ℝ) :
    quadraticDiscriminant a₀ a₁ a₂ = 4 * turan a₀ a₁ a₂ := by
  unfold quadraticDiscriminant turan
  ring

theorem quadraticDiscriminant_nonneg_iff_turan_nonneg
    (a₀ a₁ a₂ : ℝ) :
    0 ≤ quadraticDiscriminant a₀ a₁ a₂ ↔ 0 ≤ turan a₀ a₁ a₂ := by
  rw [quadraticDiscriminant_eq_four_turan]
  constructor <;> intro h <;> nlinarith

/-- The logarithmic-curvature numerator is the negative Turán expression. -/
def logCurvatureNumerator (a₀ a₁ a₂ : ℝ) : ℝ :=
  a₂ * a₀ - a₁ ^ 2

theorem logCurvatureNumerator_eq_neg_turan
    (a₀ a₁ a₂ : ℝ) :
    logCurvatureNumerator a₀ a₁ a₂ = -turan a₀ a₁ a₂ := by
  unfold logCurvatureNumerator turan
  ring

theorem logCurvatureNumerator_nonpos_iff_turan_nonneg
    (a₀ a₁ a₂ : ℝ) :
    logCurvatureNumerator a₀ a₁ a₂ ≤ 0 ↔ 0 ≤ turan a₀ a₁ a₂ := by
  rw [logCurvatureNumerator_eq_neg_turan]
  constructor <;> intro h <;> linarith

theorem turan_pos_of_centered_concavity
    {a₀ a₂ : ℝ} (ha₀ : 0 < a₀) (ha₂ : a₂ < 0) :
    0 < turan a₀ 0 a₂ := by
  unfold turan
  nlinarith

end

end InfoGeometry.Canonical.FiniteJensenTuranKernel
