import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Rank-two quadratic response and activity closure

The raw multiline response `Rᵢⱼ = Cᵢ Xⱼ - Kᵢ Xⱼ²` factors through the
two-dimensional latent design `(X, X²)`.  The statements here formalize the
exact algebraic structure; numerical SVD and nonlinear fitting remain
computational diagnostics.
-/
namespace InfoGeometry.Probability.DetectorRankTwoResponse

noncomputable section

open scoped BigOperators

def response {m n : ℕ} (C K : Fin m → ℝ) (X : Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ := C i * X j - K i * (X j) ^ 2

def latentDesign {n : ℕ} (X : Fin n → ℝ) (a : Fin 2) (j : Fin n) : ℝ :=
  if a = 0 then X j else (X j) ^ 2

def loadings {m : ℕ} (C K : Fin m → ℝ) (i : Fin m) (a : Fin 2) : ℝ :=
  if a = 0 then C i else -K i

theorem response_factorization {m n : ℕ} (C K : Fin m → ℝ) (X : Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    response C K X i j = ∑ a : Fin 2, loadings C K i a * latentDesign X a j := by
  simp [response, loadings, latentDesign, Fin.sum_univ_two]
  ring

theorem response_gauge_invariant {m n : ℕ} (C K : Fin m → ℝ) (X : Fin n → ℝ)
    (scale : ℝ) (hscale : scale ≠ 0) (i : Fin m) (j : Fin n) :
    response (fun i => C i / scale) (fun i => K i / scale ^ 2)
        (fun j => scale * X j) i j = response C K X i j := by
  simp [response]
  field_simp [hscale]

theorem restored_response {m n : ℕ} (C K : Fin m → ℝ) (X : Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    response C K X i j + K i * (X j) ^ 2 = C i * X j := by
  simp [response]

def coincidence {n : ℕ} (κ : ℝ) (X : Fin n → ℝ) (j : Fin n) : ℝ := κ * (X j) ^ 2

def closureSlope (C₁ C₂ κ : ℝ) : ℝ := C₁ * C₂ / κ

theorem product_closure {n : ℕ} (C₁ C₂ κ : ℝ) (X : Fin n → ℝ)
    (hκ : κ ≠ 0) (j : Fin n) :
    (C₁ * X j) * (C₂ * X j) = closureSlope C₁ C₂ κ * coincidence κ X j := by
  simp [closureSlope, coincidence]
  field_simp [hκ]

theorem contact_gauge_unique {n : ℕ} (X : Fin n → ℝ) (j₀ : Fin n)
    (hX : X j₀ ≠ 0) :
    (X j₀)⁻¹ * X j₀ = 1 := by
  exact inv_mul_cancel₀ hX

end
end InfoGeometry.Probability.DetectorRankTwoResponse
