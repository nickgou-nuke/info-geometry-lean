/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite frame determinants and orthogonal fiber volume

The native matrix congruence `E.transpose * G * E` carries the full reference
bilinear form. Its determinant records the square of the frame determinant,
with the reference determinant retained. No new metric or entropy carrier is
introduced.

The one-dimensional fiber result is an orthogonal block calculation. Unit
transverse determinant makes the absolute Gram-volume equal the magnitude of
the longitudinal parameter. A general nonorthogonal fiber instead requires
the Schur complement already owned by Mathlib and
`InfoGeometry.Algebra.BlockSchurFactorization`.

The final four-dimensional examples separate volume preservation from metric
preservation and from the order of composing frames. These finite identities
do not construct a manifold, a vacuum state, a Jacobian of a coordinate map,
or a distance between arbitrary points.
-/

namespace InfoGeometry.LinearAlgebra.FrameMetricDeterminant

section Congruence

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Determinant of the pullback of an arbitrary reference bilinear matrix. -/
theorem det_transpose_mul_mul (E G : Matrix n n R) :
    (E.transpose * G * E).det = E.det ^ 2 * G.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The reference determinant `-1` gives the negative squared frame determinant.
This hypothesis is a determinant normalization, not a signature classification. -/
theorem det_transpose_mul_mul_of_det_eq_neg_one
    (E G : Matrix n n R) (hG : G.det = -1) :
    (E.transpose * G * E).det = -(E.det ^ 2) := by
  rw [det_transpose_mul_mul, hG, mul_neg_one]

/-- An orthogonal longitudinal block factors from the transverse Gram matrix. -/
theorem det_negative_square_block (h : R) (H : Matrix n n R) :
    (Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => -(h ^ 2))
      (0 : Matrix (Fin 1) n R) (0 : Matrix n (Fin 1) R) H).det =
        -(h ^ 2) * H.det := by
  rw [Matrix.det_fromBlocks_zero₂₁]
  simp

end Congruence

section RealVolume

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The absolute Gram-volume density equals the absolute frame determinant
when the reference determinant is `-1`. -/
theorem sqrt_abs_det_transpose_mul_mul
    (E G : Matrix n n ℝ) (hG : G.det = -1) :
    Real.sqrt |(E.transpose * G * E).det| = |E.det| := by
  rw [det_transpose_mul_mul_of_det_eq_neg_one E G hG, abs_neg,
    abs_of_nonneg (sq_nonneg E.det), Real.sqrt_sq_eq_abs]

/-- For an orthogonal fiber with unit transverse Gram determinant, the
absolute Gram-volume is the magnitude of the longitudinal parameter. -/
theorem sqrt_abs_det_negative_square_block_of_unit_transverse
    (h : ℝ) (H : Matrix n n ℝ) (hH : H.det = 1) :
    Real.sqrt |(Matrix.fromBlocks (Matrix.of fun _ _ : Fin 1 => -(h ^ 2))
      (0 : Matrix (Fin 1) n ℝ) (0 : Matrix n (Fin 1) ℝ) H).det| = |h| := by
  rw [det_negative_square_block, hH, mul_one, abs_neg,
    abs_of_nonneg (sq_nonneg h), Real.sqrt_sq_eq_abs]

/-- A unit four-volume multiplier can change a Lorentz bilinear form. -/
theorem exists_det_one_not_preserving_lorentz_form :
    ∃ E : Matrix (Fin 4) (Fin 4) ℝ,
      E.det = 1 ∧
        E.transpose * Matrix.diagonal ![-1, 1, 1, 1] * E ≠
          Matrix.diagonal ![-1, 1, 1, 1] := by
  refine ⟨Matrix.diagonal ![2, (1 / 2 : ℝ), 1, 1], ?_, ?_⟩
  · norm_num [Matrix.det_diagonal, Fin.prod_univ_succ]
  · intro heq
    have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) heq
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h00

/-- Unit frame determinants do not determine the order of frame composition.
The diagonal frame `diag(2, 1/2, 1, 1)` does not commute with the shear
`I + E₀₁`, implemented by adding row `1` of the identity to row `0`.
Both are invertible volume-preserving frames because their determinants are
one; their products differ in entry `(0, 1)`. -/
theorem exists_det_one_frames_not_commuting :
    ∃ E F : Matrix (Fin 4) (Fin 4) ℝ,
      E * F ≠ F * E ∧ E.det = 1 ∧ F.det = 1 := by
  let E : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.diagonal ![2, (1 / 2 : ℝ), 1, 1]
  let F : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.updateRow (1 : Matrix (Fin 4) (Fin 4) ℝ) 0
      ((1 : Matrix (Fin 4) (Fin 4) ℝ) 0 +
        (1 : Matrix (Fin 4) (Fin 4) ℝ) 1)
  refine ⟨E, F, ?_, ?_, ?_⟩
  · intro heq
    have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) heq
    norm_num [E, F, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at h01
  · norm_num [E, Matrix.det_diagonal, Fin.prod_univ_succ]
  · dsimp only [F]
    rw [Matrix.det_updateRow_add_self _ (show (0 : Fin 4) ≠ 1 by decide),
      Matrix.det_one]

end RealVolume

end InfoGeometry.LinearAlgebra.FrameMetricDeterminant
