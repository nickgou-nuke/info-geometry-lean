import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Doubled covariance projection and reflection

This is the finite operator-algebra core of the covariance-to-Krein
construction.  It is stated for two operator roots `R` and `T` satisfying
`R * R + T * T = 1`; no diagonalisation or commutativity assumption is used.
An analytic theorem extracting these roots from a positive operator is a
separate functional-calculus layer and is intentionally not asserted here.
-/

noncomputable section

namespace InfoGeometry.Krein

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The doubled covariance projection built from complementary amplitudes. -/
def doubledCovarianceProjection (R T : Matrix n n ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (R * R) (R * T) (T * R) (T * T)

theorem doubledCovarianceProjection_sq (R T : Matrix n n ℝ)
    (hsum : R * R + T * T = 1) :
    doubledCovarianceProjection R T * doubledCovarianceProjection R T =
      doubledCovarianceProjection R T := by
  rw [doubledCovarianceProjection, Matrix.fromBlocks_multiply]
  have h₁ : R * R * (R * R) + R * T * (T * R) = R * R := by
    calc
      R * R * (R * R) + R * T * (T * R) =
          R * (R * R + T * T) * R := by noncomm_ring
      _ = R * 1 * R := by rw [hsum]
      _ = R * R := by simp
  have h₂ : R * R * (R * T) + R * T * (T * T) = R * T := by
    calc
      R * R * (R * T) + R * T * (T * T) =
          R * (R * R + T * T) * T := by noncomm_ring
      _ = R * 1 * T := by rw [hsum]
      _ = R * T := by simp
  have h₃ : T * R * (R * R) + T * T * (T * R) = T * R := by
    calc
      T * R * (R * R) + T * T * (T * R) =
          T * (R * R + T * T) * R := by noncomm_ring
      _ = T * 1 * R := by rw [hsum]
      _ = T * R := by simp
  have h₄ : T * R * (R * T) + T * T * (T * T) = T * T := by
    calc
      T * R * (R * T) + T * T * (T * T) =
          T * (R * R + T * T) * T := by noncomm_ring
      _ = T * 1 * T := by rw [hsum]
      _ = T * T := by simp
  simp only [h₁, h₂, h₃, h₄]

omit [DecidableEq n] in
theorem doubledCovarianceProjection_transpose
    (R T : Matrix n n ℝ)
    (hR : R.transpose = R) (hT : T.transpose = T) :
    (doubledCovarianceProjection R T).transpose =
      doubledCovarianceProjection R T := by
  simp [doubledCovarianceProjection, Matrix.fromBlocks_transpose,
    transpose_mul, hR, hT]

/-- The fundamental symmetry associated with the doubled projection. -/
def doubledCovarianceSymmetry (R T : Matrix n n ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  2 • doubledCovarianceProjection R T - 1

theorem doubledCovarianceSymmetry_sq (R T : Matrix n n ℝ)
    (hsum : R * R + T * T = 1) :
    doubledCovarianceSymmetry R T * doubledCovarianceSymmetry R T = 1 := by
  let P := doubledCovarianceProjection R T
  have hP : P * P = P := doubledCovarianceProjection_sq R T hsum
  change (2 • P - 1) * (2 • P - 1) = 1
  calc
    (2 • P - 1) * (2 • P - 1) =
        4 • (P * P) - 4 • P + 1 := by noncomm_ring
    _ = 4 • P - 4 • P + 1 := by rw [hP]
    _ = 1 := by noncomm_ring

end InfoGeometry.Krein
