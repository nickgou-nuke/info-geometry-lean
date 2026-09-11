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

/-- Gauge invariance of the product closure slope H. -/
theorem closureSlope_gauge_invariant (C₁ C₂ κ l : ℝ) (hl : l ≠ 0) (hκ : κ ≠ 0) :
    closureSlope (C₁ / l) (C₂ / l) (κ / l ^ 2) = closureSlope C₁ C₂ κ := by
  simp [closureSlope]
  field_simp [hl, hκ]

/-- Absolute activity derived from the closure slope and nuclear cascade branching factors. -/
def activity (H P₁ P₂ P₁₂ W : ℝ) : ℝ := H * (P₁₂ * W) / (P₁ * P₂)

/-- Gauge invariance of the absolute activity. -/
theorem activity_gauge_invariant (C₁ C₂ κ l P₁ P₂ P₁₂ W : ℝ)
    (hl : l ≠ 0) (hκ : κ ≠ 0) :
    activity (closureSlope (C₁ / l) (C₂ / l) (κ / l ^ 2)) P₁ P₂ P₁₂ W =
    activity (closureSlope C₁ C₂ κ) P₁ P₂ P₁₂ W := by
  rw [closureSlope_gauge_invariant C₁ C₂ κ l hl hκ]

/-- Linear transformation of the rank-two latent design basis Z' = M Z. -/
def transformBasis {n : ℕ} (M : Fin 2 → Fin 2 → ℝ) (Z : Fin 2 → Fin n → ℝ)
    (b : Fin 2) (j : Fin n) : ℝ :=
  ∑ a : Fin 2, M b a * Z a j

/-- Dual transformation of loadings B' = B Minv. -/
def transformLoadings {m : ℕ} (B : Fin m → Fin 2 → ℝ) (Minv : Fin 2 → Fin 2 → ℝ)
    (i : Fin m) (b : Fin 2) : ℝ :=
  ∑ a : Fin 2, B i a * Minv a b

/-- Exact basis rotation / GL(2) invariance of the rank-two response. -/
theorem rank_two_basis_rotation {m n : ℕ} (B : Fin m → Fin 2 → ℝ) (Z : Fin 2 → Fin n → ℝ)
    (M Minv : Fin 2 → Fin 2 → ℝ)
    (h00 : Minv 0 0 * M 0 0 + Minv 0 1 * M 1 0 = 1)
    (h01 : Minv 0 0 * M 0 1 + Minv 0 1 * M 1 1 = 0)
    (h10 : Minv 1 0 * M 0 0 + Minv 1 1 * M 1 0 = 0)
    (h11 : Minv 1 0 * M 0 1 + Minv 1 1 * M 1 1 = 1)
    (i : Fin m) (j : Fin n) :
    (∑ b : Fin 2, transformLoadings B Minv i b * transformBasis M Z b j) =
    (∑ a : Fin 2, B i a * Z a j) := by
  simp [transformLoadings, transformBasis, Fin.sum_univ_two]
  linear_combination B i 0 * Z 0 j * h00 + B i 0 * Z 1 j * h01 + B i 1 * Z 0 j * h10 + B i 1 * Z 1 j * h11

/-- Physical coordinate identification: knowing Q = κ X² and contact X(j₀) = 1
    uniquely selects the quadratic coordinate from any linear combination. -/
theorem quadratic_coordinate_identification {n : ℕ} (κ : ℝ) (X : Fin n → ℝ)
    (j : Fin n) (hκ : κ ≠ 0) :
    coincidence κ X j / κ = (X j) ^ 2 := by
  simp [coincidence]
  field_simp [hκ]

#print axioms response_factorization
#print axioms response_gauge_invariant
#print axioms restored_response
#print axioms product_closure
#print axioms contact_gauge_unique
#print axioms closureSlope_gauge_invariant
#print axioms activity_gauge_invariant
#print axioms rank_two_basis_rotation
#print axioms quadratic_coordinate_identification

end
end InfoGeometry.Probability.DetectorRankTwoResponse
