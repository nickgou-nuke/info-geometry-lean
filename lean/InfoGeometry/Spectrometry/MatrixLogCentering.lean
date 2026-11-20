/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.TableBalancing
import InfoGeometry.Spectrometry.LogLeastSquares
import InfoGeometry.Probability.BipartiteLogCoupling

/-!
# The matrix and entrywise representations of finite table centering

`Probability.BipartiteLogCoupling.interaction` is the existing rectangular
matrix operator `(1 - average I) * X * (1 - average J)`.
`TableBalancing.doubleCenter` expresses the same operation through finite
row, column, and grand means. The bridge below expands the actual matrix
products; it does not assume an identification of these operators.

No positivity or nonempty-index hypothesis is needed for these identities.
The matrices have finite real index types, with decidable equality for the
matrix identity used in `center`. Optimality of the additive fit remains the
separate nonempty-table result in `LogLeastSquares`.
-/

namespace InfoGeometry.Spectrometry.MatrixLogCentering

open scoped BigOperators
open InfoGeometry.Probability.BipartiteLogCoupling (average center interaction)
open InfoGeometry.Spectrometry.TableBalancing
  (mean rowMean colMean grandMean doubleCenter)

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Left multiplication by the averaging matrix computes column means. -/
theorem average_mul_apply (X : Matrix I J ℝ) (i : I) (j : J) :
    (average I * X) i j = colMean X j := by
  change (∑ k, (Fintype.card I : ℝ)⁻¹ * X k j) =
    (∑ k, X k j) / (Fintype.card I : ℝ)
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- Right multiplication by the averaging matrix computes row means. -/
theorem mul_average_apply (X : Matrix I J ℝ) (i : I) (j : J) :
    (X * average J) i j = rowMean X i := by
  change (∑ k, X i k * (Fintype.card J : ℝ)⁻¹) =
    (∑ k, X i k) / (Fintype.card J : ℝ)
  rw [← Finset.sum_mul, div_eq_mul_inv]

/-- Averaging on both sides computes the grand mean at every entry. -/
theorem average_mul_average_apply (X : Matrix I J ℝ) (i : I) (j : J) :
    (average I * X * average J) i j = grandMean X := by
  rw [Matrix.mul_assoc, average_mul_apply]
  change (∑ k, (X * average J) k j) / (Fintype.card I : ℝ) = grandMean X
  simp_rw [mul_average_apply]
  rfl

variable [DecidableEq I] [DecidableEq J]

/-- The existing matrix interaction is exactly the entrywise centered table. -/
theorem interaction_apply_eq_doubleCenter (X : Matrix I J ℝ) (i : I) (j : J) :
    interaction X i j = doubleCenter X i j := by
  have hexpand : interaction X =
      X - average I * X - X * average J + average I * X * average J := by
    simp only [interaction, center, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hexpand]
  change X i j - (average I * X) i j - (X * average J) i j +
    (average I * X * average J) i j = doubleCenter X i j
  rw [average_mul_apply X i j, mul_average_apply X i j,
    average_mul_average_apply X i j]
  unfold doubleCenter
  ring

/-- Equality of the two operators as rectangular real-valued tables. -/
theorem interaction_eq_doubleCenter (X : Matrix I J ℝ) :
    interaction X = doubleCenter X := by
  funext i j
  exact interaction_apply_eq_doubleCenter X i j

/-- The additive least-squares fitted table is the complementary matrix component.
The identity is algebraic; the minimization theorem separately assumes nonempty
row and column types. -/
theorem additiveFit_eq_sub_interaction (X : Matrix I J ℝ) :
    LogLeastSquares.additiveFit X = X - interaction X := by
  funext i j
  change LogLeastSquares.additiveFit X i j = X i j - interaction X i j
  rw [interaction_apply_eq_doubleCenter]
  unfold LogLeastSquares.additiveFit doubleCenter
  ring

end

end InfoGeometry.Spectrometry.MatrixLogCentering
