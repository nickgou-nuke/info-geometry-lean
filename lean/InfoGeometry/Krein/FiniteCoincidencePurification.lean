import InfoGeometry.Krein.DoubledCovarianceReflection

/-!
# Finite coincidence purification

This owner keeps the finite, genuinely operatorial part of the
covariance-to-Krein construction.  A pair of (not necessarily commuting)
finite real matrices `R` and `T` satisfying

`R * R + T * T = 1`

defines an idempotent on the doubled carrier.  Its affine reflection `2 P - 1`
is a self-adjoint involution whenever `R` and `T` are self-transpose.

No scalar probability model, analytic square-root extraction, CAR
representation, or von Neumann standard-form theorem is claimed here.  The
functional-calculus step producing particular `R = sqrt C` and
`T = sqrt (1 - C)` is an upstream theorem and is intentionally separate.
-/

namespace InfoGeometry.Krein.FiniteCoincidencePurification

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev FiniteDoubledMatrix (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix (n ⊕ n) (n ⊕ n) ℝ

/-- The doubled projection associated with finite covariance amplitudes. -/
def projection (R T : Matrix n n ℝ) : FiniteDoubledMatrix n :=
  doubledCovarianceProjection R T

@[simp] theorem projection_apply (R T : Matrix n n ℝ) :
    projection R T =
      Matrix.fromBlocks (R * R) (R * T) (T * R) (T * T) := rfl

theorem projection_idempotent (R T : Matrix n n ℝ)
    (hsum : R * R + T * T = 1) :
    projection R T * projection R T = projection R T := by
  exact doubledCovarianceProjection_sq R T hsum

theorem projection_transpose (R T : Matrix n n ℝ)
    (hR : R.transpose = R) (hT : T.transpose = T) :
    (projection R T).transpose = projection R T := by
  exact doubledCovarianceProjection_transpose R T hR hT

/-- The data-dependent fundamental symmetry on the doubled finite carrier. -/
def fundamentalSymmetry (R T : Matrix n n ℝ) : FiniteDoubledMatrix n :=
  doubledCovarianceSymmetry R T

theorem fundamentalSymmetry_square (R T : Matrix n n ℝ)
    (hsum : R * R + T * T = 1) :
    fundamentalSymmetry R T * fundamentalSymmetry R T = 1 := by
  exact doubledCovarianceSymmetry_sq R T hsum

theorem fundamentalSymmetry_transpose (R T : Matrix n n ℝ)
    (hR : R.transpose = R) (hT : T.transpose = T) :
    (fundamentalSymmetry R T).transpose = fundamentalSymmetry R T := by
  simp [fundamentalSymmetry, doubledCovarianceSymmetry,
    Matrix.transpose_sub, Matrix.transpose_one,
    doubledCovarianceProjection_transpose R T hR hT]
  noncomm_ring

/-- The finite fundamental symmetry fixes its purified projection on the left. -/
theorem fundamentalSymmetry_mul_projection (R T : Matrix n n ℝ)
    (hsum : R * R + T * T = 1) :
    fundamentalSymmetry R T * projection R T = projection R T := by
  exact doubledCovarianceSymmetry_mul_projection R T hsum

/-- The finite fundamental symmetry fixes its purified projection on the right. -/
theorem projection_mul_fundamentalSymmetry (R T : Matrix n n ℝ)
    (hsum : R * R + T * T = 1) :
    projection R T * fundamentalSymmetry R T = projection R T := by
  exact doubledCovarianceProjection_mul_symmetry R T hsum

end InfoGeometry.Krein.FiniteCoincidencePurification
