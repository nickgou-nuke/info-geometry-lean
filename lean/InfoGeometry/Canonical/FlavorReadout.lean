/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import Mathlib.Basic.Real.Star
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith

/-!
# Real rectangular operator readouts and frame covariance

For a real matrix `T : Matrix m n ℝ` and column frames `L : Matrix n p ℝ`
and `R : Matrix m q ℝ`, the readout is `(T * L)ᵀ * R`. Its entries pair the
actual image of a left column with a right column. Arbitrary changes of the
two column frames induce the corresponding two-sided matrix transformation.

Orthogonal ambient transport and the two Gram transformation laws are proved
with native matrix operations and `Matrix.orthogonalGroup`. In particular,
the operator products are not replaced by commuting scalar data.

A matrix-valued readout that is even under negation of the left frame cannot
also satisfy the signed orthogonal frame law unless it vanishes. An explicit
entrywise-squared readout exhibits this obstruction on a nonzero off-diagonal
matrix. This file makes no identification with an octonion associator, no
claim about Lie-group integration, and no physical mass or mixing prediction.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.FlavorReadout

open Matrix

variable {m n p q p' q' : Type*}
variable [Fintype m] [Fintype n]

/-- Pair the images of left-frame columns with right-frame columns. -/
def readout (T : Matrix m n ℝ) (L : Matrix n p ℝ) (R : Matrix m q ℝ) :
    Matrix p q ℝ :=
  (T * L)ᵀ * R

/-- Entrywise interpretation in the ambient real dot product. -/
theorem readout_apply (T : Matrix m n ℝ) (L : Matrix n p ℝ)
    (R : Matrix m q ℝ) (a : p) (b : q) :
    readout T L R a b = (fun i => (T * L) i a) ⬝ᵥ (fun i => R i b) := rfl

@[simp] theorem readout_neg_left (T : Matrix m n ℝ) (L : Matrix n p ℝ)
    (R : Matrix m q ℝ) : readout T (-L) R = -readout T L R := by
  simp only [readout, Matrix.mul_neg, Matrix.transpose_neg, Matrix.neg_mul]

@[simp] theorem readout_neg_right (T : Matrix m n ℝ) (L : Matrix n p ℝ)
    (R : Matrix m q ℝ) : readout T L (-R) = -readout T L R := by
  simp only [readout, Matrix.mul_neg]

@[simp] theorem readout_neg_neg (T : Matrix m n ℝ) (L : Matrix n p ℝ)
    (R : Matrix m q ℝ) : readout T (-L) (-R) = readout T L R := by
  rw [readout_neg_left, readout_neg_right, neg_neg]

/-- General covariance; the column-change matrices need not be square or invertible. -/
theorem readout_basis_change [Fintype p] [Fintype q]
    (T : Matrix m n ℝ) (L : Matrix n p ℝ) (R : Matrix m q ℝ)
    (U : Matrix p p' ℝ) (V : Matrix q q' ℝ) :
    readout T (L * U) (R * V) = Uᵀ * readout T L R * V := by
  simp only [readout, Matrix.transpose_mul, Matrix.mul_assoc]

/-- An output isometry and an actual operator intertwiner preserve the readout. -/
theorem readout_intertwining [DecidableEq m]
    (T T' : Matrix m n ℝ) (L : Matrix n p ℝ) (R : Matrix m q ℝ)
    (U : Matrix m m ℝ) (V : Matrix n n ℝ)
    (hU : Uᵀ * U = 1) (hinter : T' * V = U * T) :
    readout T' (V * L) (U * R) = readout T L R := by
  calc
    readout T' (V * L) (U * R) = ((T' * V) * L)ᵀ * (U * R) := by
      simp only [readout, Matrix.mul_assoc]
    _ = ((U * T) * L)ᵀ * (U * R) := by rw [hinter]
    _ = (T * L)ᵀ * (Uᵀ * U) * R := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = readout T L R := by
      simp only [hU, Matrix.mul_one, readout]

/-- Independent native orthogonal changes in domain and codomain transport `T` and both frames. -/
theorem readout_orthogonal_transport [DecidableEq m] [DecidableEq n]
    (T : Matrix m n ℝ) (L : Matrix n p ℝ) (R : Matrix m q ℝ)
    (U : Matrix.orthogonalGroup m ℝ) (V : Matrix.orthogonalGroup n ℝ) :
    readout ((U : Matrix m m ℝ) * T * (V : Matrix n n ℝ)ᵀ)
        ((V : Matrix n n ℝ) * L) ((U : Matrix m m ℝ) * R) =
      readout T L R := by
  apply readout_intertwining
  · exact Matrix.mem_orthogonalGroup_iff'.mp U.property
  · rw [Matrix.mul_assoc, Matrix.mem_orthogonalGroup_iff'.mp V.property,
      Matrix.mul_one]

/-- The right orthogonal factor cancels from the left Gram matrix. -/
theorem left_gram_basis_change [Fintype p] [Fintype q] [DecidableEq q]
    (Y : Matrix p q ℝ) (U : Matrix p p ℝ) (V : Matrix q q ℝ)
    (hV : V * Vᵀ = 1) :
    (Uᵀ * Y * V) * (Uᵀ * Y * V)ᵀ = Uᵀ * (Y * Yᵀ) * U := by
  calc
    (Uᵀ * Y * V) * (Uᵀ * Y * V)ᵀ =
        (Uᵀ * Y) * (V * Vᵀ) * (Yᵀ * U) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = Uᵀ * (Y * Yᵀ) * U := by
      rw [hV, Matrix.mul_one]
      simp only [Matrix.mul_assoc]

/-- The left orthogonal factor cancels from the right Gram matrix. -/
theorem right_gram_basis_change [Fintype p] [Fintype q] [DecidableEq p]
    (Y : Matrix p q ℝ) (U : Matrix p p ℝ) (V : Matrix q q ℝ)
    (hU : U * Uᵀ = 1) :
    (Uᵀ * Y * V)ᵀ * (Uᵀ * Y * V) = Vᵀ * (Yᵀ * Y) * V := by
  calc
    (Uᵀ * Y * V)ᵀ * (Uᵀ * Y * V) =
        (Vᵀ * Yᵀ) * (U * Uᵀ) * (Y * V) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = Vᵀ * (Yᵀ * Y) * V := by
      rw [hU, Matrix.mul_one]
      simp only [Matrix.mul_assoc]

/-- Readout left-Gram covariance under native orthogonal frame changes. -/
theorem readout_left_gram [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (T : Matrix m n ℝ) (L : Matrix n p ℝ) (R : Matrix m q ℝ)
    (U : Matrix.orthogonalGroup p ℝ) (V : Matrix.orthogonalGroup q ℝ) :
    readout T (L * (U : Matrix p p ℝ)) (R * (V : Matrix q q ℝ)) *
        (readout T (L * (U : Matrix p p ℝ)) (R * (V : Matrix q q ℝ)))ᵀ =
      (U : Matrix p p ℝ)ᵀ * (readout T L R * (readout T L R)ᵀ) *
        (U : Matrix p p ℝ) := by
  simpa only [readout_basis_change] using
    left_gram_basis_change (readout T L R) (U : Matrix p p ℝ) (V : Matrix q q ℝ)
      (Matrix.mem_orthogonalGroup_iff.mp V.property)

/-- Readout right-Gram covariance under native orthogonal frame changes. -/
theorem readout_right_gram [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (T : Matrix m n ℝ) (L : Matrix n p ℝ) (R : Matrix m q ℝ)
    (U : Matrix.orthogonalGroup p ℝ) (V : Matrix.orthogonalGroup q ℝ) :
    (readout T (L * (U : Matrix p p ℝ)) (R * (V : Matrix q q ℝ)))ᵀ *
        readout T (L * (U : Matrix p p ℝ)) (R * (V : Matrix q q ℝ)) =
      (V : Matrix q q ℝ)ᵀ * ((readout T L R)ᵀ * readout T L R) *
        (V : Matrix q q ℝ) := by
  simpa only [readout_basis_change] using
    right_gram_basis_change (readout T L R) (U : Matrix p p ℝ) (V : Matrix q q ℝ)
      (Matrix.mem_orthogonalGroup_iff.mp U.property)

/-- Evenness in the left frame and signed orthogonal covariance force every entry to vanish.
Only the orthogonal changes `-1` and `1` are needed for this obstruction. -/
theorem eq_zero_of_even_left_and_orthogonal_covariance
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (F : Matrix n p ℝ → Matrix m q ℝ → Matrix p q ℝ)
    (heven : ∀ L R, F (-L) R = F L R)
    (hcov : ∀ (L : Matrix n p ℝ) (R : Matrix m q ℝ)
      (U : Matrix p p ℝ) (V : Matrix q q ℝ),
      U ∈ Matrix.orthogonalGroup p ℝ → V ∈ Matrix.orthogonalGroup q ℝ →
      F (L * U) (R * V) = Uᵀ * F L R * V)
    (L : Matrix n p ℝ) (R : Matrix m q ℝ) : F L R = 0 := by
  have hneg : (-1 : Matrix p p ℝ) ∈ Matrix.orthogonalGroup p ℝ := by
    apply Matrix.mem_orthogonalGroup_iff.mpr
    simp
  have hone : (1 : Matrix q q ℝ) ∈ Matrix.orthogonalGroup q ℝ := by
    apply Matrix.mem_orthogonalGroup_iff.mpr
    simp
  have hodd : F (-L) R = -F L R := by
    simpa only [Matrix.mul_neg, Matrix.mul_one, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul] using
      hcov L R (-1) 1 hneg hone
  have hself : F L R = -F L R := (heven L R).symm.trans hodd
  ext i j
  have hij := congrArg (fun M : Matrix p q ℝ => M i j) hself
  change F L R i j = -F L R i j at hij
  change F L R i j = 0
  linarith

/-- Squaring each scalar readout entry discards its sign. This is not a norm on operators. -/
def squaredReadout (T : Matrix m n ℝ) (L : Matrix n p ℝ) (R : Matrix m q ℝ) :
    Matrix p q ℝ :=
  (readout T L R).map (fun x => x ^ 2)

@[simp] theorem squaredReadout_neg_left (T : Matrix m n ℝ) (L : Matrix n p ℝ)
    (R : Matrix m q ℝ) : squaredReadout T (-L) R = squaredReadout T L R := by
  ext i j
  simp [squaredReadout]

/-- A concrete nonzero off-diagonal readout violates the signed law after entrywise squaring. -/
theorem squaredReadout_counterexample :
    squaredReadout (MatrixTwoNoncommutativity.upperUnit (R := ℝ))
        (-(1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 ≠
      (-(1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ *
        squaredReadout (MatrixTwoNoncommutativity.upperUnit (R := ℝ)) 1 1 := by
  intro h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) h
  norm_num [squaredReadout, readout, MatrixTwoNoncommutativity.upperUnit,
    Matrix.mul_apply, Fin.sum_univ_two] at h10

/-- The actual real matrix carrier has a closed noncommutativity witness. -/
theorem matrix_carrier_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨MatrixTwoNoncommutativity.upperUnit, MatrixTwoNoncommutativity.lowerUnit,
    MatrixTwoNoncommutativity.matrix_two_noncommutative⟩

end InfoGeometry.Canonical.FlavorReadout
