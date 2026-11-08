import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-!
# Rank-two quadratic response and activity closure

Floating-point SVD is used only to diagnose the numerical data matrix.
The measured response is tested against an algebraic two-dimensional model of
coincidence-summed detector response:
  `Rᵢⱼ = Cᵢ Xⱼ - Kᵢ Xⱼ²`,  `Zⱼ = (Xⱼ, Xⱼ²)ᵀ`.

Consequently, every 3×3 minor of an exact model matrix vanishes. These identities characterize the proposed model; they do not by themselves establish that an experimental matrix is exactly rank two. The
representation is invariant under `Z ↦ M Z`, `B ↦ B M⁻¹` for `M ∈ GL₂(ℝ)`,
and the closure slope
  `H = C₁ C₂ / κ`
is invariant under the dilation gauge
  `X ↦ λ X`, `Cᵢ ↦ Cᵢ / λ`, `Kᵢ ↦ Kᵢ / λ²`, `κ ↦ κ / λ²`.

These are exact algebraic properties of the proposed response model. The
experimental data support the model through residuals, scale comparisons, and
activity validation; they do not become exact merely because the algebraic
model has exact invariants.
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

/-- Recovery of the true physical source activity A under microscopic cascade calibration. -/
theorem activity_recovers_activity (A P₁ P₂ P₁₂ W ε₁ ε₂ : ℝ)
    (hA : A ≠ 0) (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0) (hP₁₂ : P₁₂ ≠ 0) (hW : W ≠ 0)
    (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) :
    let C₁ := A * P₁ * ε₁
    let C₂ := A * P₂ * ε₂
    let κ := A * P₁₂ * W * ε₁ * ε₂
    activity (closureSlope C₁ C₂ κ) P₁ P₂ P₁₂ W = A := by
  intro C₁ C₂ κ
  dsimp [activity, closureSlope, C₁, C₂, κ]
  field_simp

/-- Effective gamma branching factor under secondary internal conversion coefficient α. -/
def photonBranchOfConversion (α : ℝ) : ℝ := 1 / (1 + α)

/-- Absolute coincidence activity in the presence of secondary internal conversion. -/
theorem activity_with_conversion (H W P₁ P₂ b_feed α : ℝ)
    (hα : 1 + α ≠ 0) (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0) :
    let P₁₂ := P₁ * b_feed * photonBranchOfConversion α
    activity H P₁ P₂ P₁₂ W = H * (W * b_feed) / (P₂ * (1 + α)) := by
  intro P₁₂
  dsimp [activity, P₁₂, photonBranchOfConversion]
  field_simp

/-- Explicit constructive linear dependence of any three spectral lines in the rank-two response. -/
theorem three_line_linear_dependence {n : ℕ} (C₁ C₂ C₃ K₁ K₂ K₃ : ℝ) (X : Fin n → ℝ) (j : Fin n) :
    (C₂ * K₃ - C₃ * K₂) * (C₁ * X j - K₁ * (X j) ^ 2) +
    (C₃ * K₁ - C₁ * K₃) * (C₂ * X j - K₂ * (X j) ^ 2) +
    (C₁ * K₂ - C₂ * K₁) * (C₃ * X j - K₃ * (X j) ^ 2) = 0 := by
  ring

/-- Explicit constructive linear dependence of any three geometry columns in the rank-two response. -/
theorem three_geometry_linear_dependence (C K X₁ X₂ X₃ : ℝ) :
    (X₂ * X₃ ^ 2 - X₃ * X₂ ^ 2) * (C * X₁ - K * X₁ ^ 2) +
    (X₃ * X₁ ^ 2 - X₁ * X₃ ^ 2) * (C * X₂ - K * X₂ ^ 2) +
    (X₁ * X₂ ^ 2 - X₂ * X₁ ^ 2) * (C * X₃ - K * X₃ ^ 2) = 0 := by
  ring

/-- The 3-by-3 submatrix formed by any three lines and three geometries in the rank-two response. -/
def matrix3x3 (C K : Fin 3 → ℝ) (X : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => C i * X j - K i * (X j) ^ 2

/-- Exact vanishing of every 3-by-3 minor of the multiline quadratic response matrix. -/
theorem det_matrix3x3_zero (C K : Fin 3 → ℝ) (X : Fin 3 → ℝ) :
    (matrix3x3 C K X).det = 0 := by
  simp [Matrix.det_fin_three, matrix3x3]
  ring

end
end InfoGeometry.Probability.DetectorRankTwoResponse
