import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Chiral operator for time-ordered coincidence data

For a lagged coincidence matrix `F`, the doubled operator

`D F = [[0, F], [Fᵀ, 0]]`

is symmetric even when `F` is not.  Its square keeps the source and target
Gram operators separate.  This is the finite noncommutative block-algebra
core of the time-oriented construction; no detailed-balance or stochastic
interpretation is assumed.
-/

namespace InfoGeometry.Krein

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev DoubledLaggedMatrix (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix (n ⊕ n) (n ⊕ n) ℝ

/-- The symmetric doubled operator associated with an oriented lagged matrix. -/
def laggedCoincidenceDirac (F : Matrix n n ℝ) : DoubledLaggedMatrix n :=
  Matrix.fromBlocks 0 F F.transpose 0

/-- Off-diagonal observation embedding for a latent left/right factor pair. -/
def laggedFactorEmbedding (L R : Matrix n n ℝ) : DoubledLaggedMatrix n :=
  Matrix.fromBlocks 0 L R 0

theorem laggedCoincidenceDirac_triFactor_congruence
    (L S R : Matrix n n ℝ) :
    laggedCoincidenceDirac (L * S.transpose * R.transpose) =
        laggedFactorEmbedding L R * laggedCoincidenceDirac S *
        (laggedFactorEmbedding L R).transpose := by
  simp [laggedCoincidenceDirac, laggedFactorEmbedding,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
    Matrix.mul_assoc]

/-- The source/target grading on the doubled carrier. -/
def laggedCoincidenceGrading : DoubledLaggedMatrix n :=
  Matrix.fromBlocks 1 0 0 (-1)

theorem laggedCoincidenceDirac_transpose (F : Matrix n n ℝ) :
    (laggedCoincidenceDirac F).transpose = laggedCoincidenceDirac F := by
  simp [laggedCoincidenceDirac, Matrix.fromBlocks_transpose]

theorem laggedCoincidenceDirac_square (F : Matrix n n ℝ) :
    laggedCoincidenceDirac F * laggedCoincidenceDirac F =
      Matrix.fromBlocks (F * F.transpose) 0 0 (F.transpose * F) := by
  rw [laggedCoincidenceDirac, Matrix.fromBlocks_multiply]
  simp

theorem laggedCoincidenceGrading_square :
    laggedCoincidenceGrading (n := n) * laggedCoincidenceGrading (n := n) = 1 := by
  rw [laggedCoincidenceGrading, Matrix.fromBlocks_multiply]
  simp

theorem laggedCoincidenceGrading_anticommutes (F : Matrix n n ℝ) :
    laggedCoincidenceGrading (n := n) * laggedCoincidenceDirac F =
      -(laggedCoincidenceDirac F * laggedCoincidenceGrading (n := n)) := by
  rw [laggedCoincidenceGrading, laggedCoincidenceDirac,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

end InfoGeometry.Krein
