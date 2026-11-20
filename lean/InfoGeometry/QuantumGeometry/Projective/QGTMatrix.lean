/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGeometry.Projective.QGT
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Basic.Complex.BigOperators

/-!
# Finite operator families and the projective quantum geometric tensor

The matrix is indexed by a finite family of arbitrary bounded complex-linear
operators on a complete complex Hilbert space. The Hilbert space itself need
not be finite-dimensional. Its entries are the existing projective QGT, and
positivity is proved by identifying it with the native Gram matrix of the
horizontal operator-state vectors.

Coefficient matrices use a column convention: for `C : Matrix ι κ ℂ`, the new
operator with index `j : κ` is `∑ i, C i j • X i`. Consequently the QGT matrix
transforms as `Cᴴ * Q * C`. Real coefficients transport both the real metric
and the repository's Berry convention `Ω = -2 Im Q` by `Cᵀ * M * C`.

The skew-adjoint commutator theorem retains the convention of the existing
QGT owner. These finite-family results neither construct unbounded spacetime
operators nor assert positivity for an indefinite spacetime or Krein form.
-/

noncomputable section

open Matrix InnerProductSpace
open scoped BigOperators ComplexOrder

namespace InfoGeometry.QuantumGeometry.Projective

variable {H ι κ : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-- The existing projective QGT evaluated on every ordered pair of operators. -/
def qgtMatrix (ψ : NormalizedState H) (X : ι → EndH) : Matrix ι ι ℂ :=
  fun i j => QGT ψ (X i) (X j)

/-- The real metric on a family of horizontal operator-state vectors. -/
def qgtMetricMatrix (ψ : NormalizedState H) (X : ι → EndH) : Matrix ι ι ℝ :=
  fun i j => fubiniStudyMetric ψ (X i) (X j)

/-- The Berry matrix uses precisely the existing convention `Ω = -2 Im Q`. -/
def qgtBerryMatrix (ψ : NormalizedState H) (X : ι → EndH) : Matrix ι ι ℝ :=
  fun i j => berryCurvature ψ (X i) (X j)

/-- Centering is inherited from the existing normalized projective owner. -/
theorem qgtMatrix_eq_gram (ψ : NormalizedState H) (X : ι → EndH) :
    qgtMatrix ψ X = Matrix.gram ℂ (fun i => projOrth ψ (X i)) := by
  ext i j
  exact QGT_eq_inner_projOrth ψ (X i) (X j)

theorem qgtMatrix_isHermitian (ψ : NormalizedState H) (X : ι → EndH) :
    (qgtMatrix ψ X).IsHermitian := by
  rw [qgtMatrix_eq_gram]
  exact Matrix.isHermitian_gram ℂ _

/-- Positivity uses the Hilbert inner product, with no operator commutativity assumption. -/
theorem qgtMatrix_posSemidef [Finite ι]
    (ψ : NormalizedState H) (X : ι → EndH) :
    (qgtMatrix ψ X).PosSemidef := by
  rw [qgtMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℂ _

/-- The full complex coefficient quadratic form is an actual squared Hilbert norm. -/
theorem qgtMatrix_quadratic_eq_norm_sq [Fintype ι]
    (ψ : NormalizedState H) (X : ι → EndH) (c : ι → ℂ) :
    dotProduct (star c) ((qgtMatrix ψ X).mulVec c) =
      (‖∑ i, c i • projOrth ψ (X i)‖ : ℂ) ^ 2 := by
  rw [qgtMatrix_eq_gram, Matrix.star_dotProduct_gram_mulVec]
  exact inner_self_eq_norm_sq_to_K _

/-- In particular, each diagonal entry is the squared norm of its horizontal vector. -/
theorem qgtMatrix_apply_self (ψ : NormalizedState H) (X : ι → EndH) (i : ι) :
    qgtMatrix ψ X i i = (‖projOrth ψ (X i)‖ : ℂ) ^ 2 := by
  change QGT ψ (X i) (X i) = _
  rw [QGT_eq_inner_projOrth]
  exact inner_self_eq_norm_sq_to_K _

/-- Multiplying the normalized state by a unit complex phase fixes the entire matrix. -/
theorem qgtMatrix_phase_invariant (ψ : NormalizedState H) (X : ι → EndH)
    (c : ℂ) (hc : starRingEnd ℂ c * c = 1) :
    qgtMatrix (phaseRotate ψ c hc) X = qgtMatrix ψ X := by
  ext i j
  exact QGT_phase_invariant ψ (X i) (X j) c hc

theorem qgtMetricMatrix_transpose (ψ : NormalizedState H) (X : ι → EndH) :
    (qgtMetricMatrix ψ X)ᵀ = qgtMetricMatrix ψ X := by
  ext i j
  have h := congrArg Complex.re ((qgtMatrix_isHermitian ψ X).apply i j)
  simpa [qgtMetricMatrix, fubiniStudyMetric, qgtMatrix, Complex.star_def] using h

theorem qgtBerryMatrix_transpose (ψ : NormalizedState H) (X : ι → EndH) :
    (qgtBerryMatrix ψ X)ᵀ = -qgtBerryMatrix ψ X := by
  ext i j
  have h : -(QGT ψ (X j) (X i)).im = (QGT ψ (X i) (X j)).im := by
    simpa [qgtMatrix, Complex.star_def] using
      congrArg Complex.im ((qgtMatrix_isHermitian ψ X).apply i j)
  change -2 * (QGT ψ (X j) (X i)).im = -(-2 * (QGT ψ (X i) (X j)).im)
  linarith

omit [CompleteSpace H] in
/-- Exact entry decomposition, with the sign fixed by `berryCurvature = -2 Im QGT`. -/
theorem qgtMatrix_apply_decomposition (ψ : NormalizedState H) (X : ι → EndH)
    (i j : ι) :
    qgtMatrix ψ X i j =
      (qgtMetricMatrix ψ X i j : ℂ) -
        (Complex.I / 2) * (qgtBerryMatrix ψ X i j : ℂ) := by
  apply Complex.ext <;>
    simp [qgtMatrix, qgtMetricMatrix, qgtBerryMatrix, fubiniStudyMetric,
      berryCurvature]

/-- Complex column coefficients form new operators before any state readout. -/
def mixOperatorFamily [Fintype ι] (C : Matrix ι κ ℂ) (X : ι → EndH) : κ → EndH :=
  fun j => ∑ i, C i j • X i

omit [CompleteSpace H] in
/-- Horizontal projection commutes with finite complex linear combinations of operators. -/
theorem projOrth_mixOperatorFamily [Fintype ι]
    (ψ : NormalizedState H) (C : Matrix ι κ ℂ) (X : ι → EndH) (j : κ) :
    projOrth ψ (mixOperatorFamily C X j) =
      ∑ i, C i j • projOrth ψ (X i) := by
  simp [projOrth, mixOperatorFamily, _root_.sum_apply, inner_sum,
    inner_smul_right, Finset.sum_smul, Finset.sum_sub_distrib, smul_sub, mul_smul]

/-- Arbitrary rectangular coefficient changes act by Hermitian congruence. -/
theorem qgtMatrix_mixOperatorFamily [Fintype ι]
    (ψ : NormalizedState H) (C : Matrix ι κ ℂ) (X : ι → EndH) :
    qgtMatrix ψ (mixOperatorFamily C X) = Cᴴ * qgtMatrix ψ X * C := by
  rw [qgtMatrix_eq_gram, qgtMatrix_eq_gram, Matrix.mul_assoc]
  ext a b
  simp only [Matrix.gram_apply, projOrth_mixOperatorFamily, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- For real column coefficients the metric transforms by ordinary congruence. -/
theorem qgtMetricMatrix_mixOperatorFamily_real [Fintype ι]
    (ψ : NormalizedState H) (C : Matrix ι κ ℝ) (X : ι → EndH) :
    qgtMetricMatrix ψ (mixOperatorFamily (C.map Complex.ofReal) X) =
      Cᵀ * qgtMetricMatrix ψ X * C := by
  ext a b
  have h := congrArg (fun M : Matrix κ κ ℂ => (M a b).re)
    (qgtMatrix_mixOperatorFamily ψ (C.map Complex.ofReal) X)
  simpa only [qgtMetricMatrix, fubiniStudyMetric, qgtMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.star_def, Complex.conj_ofReal, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using h

/-- Real coefficients transport the Berry two-form with the same index convention. -/
theorem qgtBerryMatrix_mixOperatorFamily_real [Fintype ι]
    (ψ : NormalizedState H) (C : Matrix ι κ ℝ) (X : ι → EndH) :
    qgtBerryMatrix ψ (mixOperatorFamily (C.map Complex.ofReal) X) =
      Cᵀ * qgtBerryMatrix ψ X * C := by
  ext a b
  change -2 * (qgtMatrix ψ (mixOperatorFamily (C.map Complex.ofReal) X) a b).im = _
  rw [qgtMatrix_mixOperatorFamily]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, Complex.star_def, Complex.conj_ofReal, Complex.im_sum,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    zero_add, add_zero, qgtMatrix, qgtBerryMatrix, berryCurvature,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- For skew-adjoint generators, the transpose defect is the negative commutator expectation.
The sign is the one proved in the existing projective QGT owner. -/
theorem qgtMatrix_sub_transpose_of_skewAdjoint
    (ψ : NormalizedState H) (X : ι → EndH)
    (hX : ∀ i, ContinuousLinearMap.adjoint (X i) = -(X i)) :
    qgtMatrix ψ X - (qgtMatrix ψ X)ᵀ =
      fun i j => -inner ℂ ψ.vec (opCommutator (X i) (X j) ψ.vec) := by
  ext i j
  have hswap : qgtMatrix ψ X j i = star (qgtMatrix ψ X i j) :=
    ((qgtMatrix_isHermitian ψ X).apply j i).symm
  rw [Matrix.sub_apply, Matrix.transpose_apply, hswap, Complex.star_def, Complex.sub_conj]
  rw [← berryCurvature_skewAdjoint_commutator ψ (X i) (X j) (hX i) (hX j)]
  simp only [qgtMatrix, berryCurvature]
  push_cast
  ring

end InfoGeometry.QuantumGeometry.Projective

end
