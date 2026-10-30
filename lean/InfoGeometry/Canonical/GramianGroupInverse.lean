/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GramianInverseContracts
import InfoGeometry.Singular.SquareZeroChiralHodge

/-!
# Moore–Penrose formulas from Gramian group inverses

For the existing real square-matrix carrier, an index-one Drazin witness for
either Gramian supplies a Moore–Penrose inverse. Symmetry of the witness is
derived from Drazin uniqueness, rather than imposed. The two formulas agree
by Moore–Penrose uniqueness. Existence of the Drazin witnesses remains an
explicit hypothesis; no general reverse-order law is asserted.

Dependencies: Drazin star transport and uniqueness → left Gramian formula →
Moore–Penrose star transport → right Gramian formula → agreement.
-/

namespace InfoGeometry.Canonical.GramianInverseContracts

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Singular.MoorePenrose

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Symmetry of the Gramian group inverse is automatic. -/
theorem mp_from_left_gramian_groupInverse {A H : Matrix ι ι ℝ}
    (h : IsDrazinInverse (A * A.transpose) H 1) :
    IsMoorePenroseInverse A (A.transpose * H) := by
  apply mp_from_left_gramian_drazin_one h
  have hs : star (A * A.transpose) = A * A.transpose := by
    simp only [star_real_matrix, Matrix.transpose_mul, Matrix.transpose_transpose]
  simpa only [star_real_matrix] using h.star_eq_self_of_selfAdjoint hs

/-- The right-Gramian expression follows by adjoint transport. -/
theorem mp_from_right_gramian_groupInverse {A K : Matrix ι ι ℝ}
    (h : IsDrazinInverse (A.transpose * A) K 1) :
    IsMoorePenroseInverse A (K * A.transpose) := by
  have hs : star (A.transpose * A) = A.transpose * A := by
    simp only [star_real_matrix, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hK : K.transpose = K := by
    simpa only [star_real_matrix] using h.star_eq_self_of_selfAdjoint hs
  have ht : IsDrazinInverse (A.transpose * A.transpose.transpose) K 1 := by
    simpa only [Matrix.transpose_transpose] using h
  simpa only [star_real_matrix, Matrix.transpose_mul, Matrix.transpose_transpose, hK]
    using (mp_from_left_gramian_groupInverse ht).star_same_order

/-- Both Gramian constructions give the same inverse of the original matrix. -/
theorem gramian_groupInverse_formulas_agree {A H K : Matrix ι ι ℝ}
    (hH : IsDrazinInverse (A * A.transpose) H 1)
    (hK : IsDrazinInverse (A.transpose * A) K 1) :
    A.transpose * H = K * A.transpose :=
  MoorePenrose_unique (mp_from_left_gramian_groupInverse hH)
    (mp_from_right_gramian_groupInverse hK)

end InfoGeometry.Canonical.GramianInverseContracts
