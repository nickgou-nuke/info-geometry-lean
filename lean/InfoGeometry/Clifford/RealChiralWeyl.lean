/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.RealCircularSpin
import InfoGeometry.Clifford.Cl11KleinTwist
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Real chiral Weyl matrices from the existing split atom and Pauli matrices

All matrices and coefficients in this file are real. The sheet factor uses the
existing split-atom corners, ladders, grading, and exchange. The four-dimensional
factor uses `RealCircularSpin` without introducing another Pauli basis.

The rotation and boost generators obey the displayed cyclic real Lorentz
commutator signs. Opposite corner-supported rotations have zero products.
Recovering the boosts from those families uses the internal phase operator,
not a real scalar. No real Lie-algebra classification is inferred here.

The Weyl square and the mirror-metric infinitesimal identities are finite matrix
identities. No global spin group, physical classification, or continuum operator
domain is asserted here.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealChiralWeyl

open Matrix RealCircularSpin SplitAtomDoubling GullDoranPseudoscalarBridge
open scoped Matrix Kronecker

abbrev Mat2R := Block2 ℝ
abbrev Mat8R := Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ

/-- Sheet exchange, also the cross-sheet real Krein metric matrix. -/
def mirror8 : Mat8R := (positive : Mat2R) ⊗ₖ (1 : Mat4R)

/-- The internal phase has the same orientation on the two sheets. -/
def fiberPhase8 : Mat8R := (1 : Mat2R) ⊗ₖ fiberPhase

/-- Equal rotations on the two sheets. -/
def rotation8 (a : Fin 3) : Mat8R := (1 : Mat2R) ⊗ₖ rotation a

/-- Opposite boosts on the two sheets. -/
def boost8 (a : Fin 3) : Mat8R :=
  (1 / 2 : ℝ) • ((chirality : Mat2R) ⊗ₖ sigma a)

/-- The first corner-supported rotation family. -/
def chiralSpinPlus (a : Fin 3) : Mat8R :=
  (upperCorner : Mat2R) ⊗ₖ rotation a

/-- The second corner-supported rotation family. -/
def chiralSpinMinus (a : Fin 3) : Mat8R :=
  (lowerCorner : Mat2R) ⊗ₖ rotation a

/-- The two off-diagonal Pauli solderings on the doubled real carrier. -/
def weylDirac8 (t x y z : ℝ) : Mat8R :=
  (upperLadder : Mat2R) ⊗ₖ solder t x y z +
    (lowerLadder : Mat2R) ⊗ₖ solderConjugate t x y z

private theorem kronecker_neg_left (A : Mat2R) (B : Mat4R) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  simp

private theorem kronecker_neg_right (A : Mat2R) (B : Mat4R) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  simp

private theorem kronecker_sub_left (A B : Mat2R) (C : Mat4R) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨i, r⟩ ⟨j, s⟩
  simp [sub_mul]

private theorem kronecker_sub_right (A : Mat2R) (B C : Mat4R) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨i, r⟩ ⟨j, s⟩
  simp [mul_sub]

private theorem kronecker_transpose (A : Mat2R) (B : Mat4R) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := rfl

local macro "atom_entrywise" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [positive, negative, chirality, twisted, upperCorner, lowerCorner,
      upperLadder, lowerLadder, Matrix.mul_apply, Fin.sum_univ_two]))

private theorem positive_transpose : (positive : Mat2R)ᵀ = positive := by
  atom_entrywise

private theorem chirality_transpose : (chirality : Mat2R)ᵀ = chirality := by
  atom_entrywise

private theorem positive_chirality_sandwich :
    (positive : Mat2R) * chirality * positive = -chirality := by
  atom_entrywise

private theorem positive_upperCorner_sandwich :
    (positive : Mat2R) * upperCorner * positive = lowerCorner := by
  atom_entrywise

private theorem positive_lowerCorner_sandwich :
    (positive : Mat2R) * lowerCorner * positive = upperCorner := by
  atom_entrywise

private theorem upperLadder_transpose_mul_positive :
    (upperLadder : Mat2R)ᵀ * positive = positive * upperLadder := by
  atom_entrywise

private theorem lowerLadder_transpose_mul_positive :
    (lowerLadder : Mat2R)ᵀ * positive = positive * lowerLadder := by
  atom_entrywise

private theorem mirror8_kronecker_sandwich (A : Mat2R) (B : Mat4R) :
    mirror8 * (A ⊗ₖ B) * mirror8 = (positive * A * positive) ⊗ₖ B := by
  unfold mirror8
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [one_mul, mul_one]

theorem mirror8_square : mirror8 * mirror8 = 1 := by
  unfold mirror8
  rw [← Matrix.mul_kronecker_mul, positive_square, mul_one,
    Matrix.one_kronecker_one]

theorem mirror8_transpose : mirror8ᵀ = mirror8 := by
  simp only [mirror8, kronecker_transpose, positive_transpose, Matrix.transpose_one]

theorem fiberPhase8_square : fiberPhase8 * fiberPhase8 = -1 := by
  unfold fiberPhase8
  rw [← Matrix.mul_kronecker_mul, one_mul, fiberPhase_square,
    kronecker_neg_right, Matrix.one_kronecker_one]

theorem chiralSpin_sum (a : Fin 3) :
    chiralSpinPlus a + chiralSpinMinus a = rotation8 a := by
  unfold chiralSpinPlus chiralSpinMinus rotation8
  rw [← Matrix.add_kronecker, corner_sum]

theorem fiberPhase8_mul_boost8 (a : Fin 3) :
    fiberPhase8 * boost8 a = chiralSpinPlus a - chiralSpinMinus a := by
  unfold fiberPhase8 boost8 chiralSpinPlus chiralSpinMinus
  rw [← kronecker_sub_left, corner_difference]
  simp only [rotation, quaternionAxis, Matrix.kronecker_smul, mul_smul_comm,
    ← Matrix.mul_kronecker_mul, one_mul]

theorem chiralSpinPlus_eq_half_sum (a : Fin 3) :
    chiralSpinPlus a =
      (1 / 2 : ℝ) • (rotation8 a + fiberPhase8 * boost8 a) := by
  rw [← chiralSpin_sum a, fiberPhase8_mul_boost8]
  module

theorem chiralSpinMinus_eq_half_difference (a : Fin 3) :
    chiralSpinMinus a =
      (1 / 2 : ℝ) • (rotation8 a - fiberPhase8 * boost8 a) := by
  rw [← chiralSpin_sum a, fiberPhase8_mul_boost8]
  module

theorem boost8_eq_phase_chiral_difference (a : Fin 3) :
    boost8 a = -(fiberPhase8 * (chiralSpinPlus a - chiralSpinMinus a)) := by
  rw [← fiberPhase8_mul_boost8, ← mul_assoc, fiberPhase8_square]
  simp

theorem mirror_rotation8 (a : Fin 3) :
    mirror8 * rotation8 a * mirror8 = rotation8 a := by
  unfold rotation8
  rw [mirror8_kronecker_sandwich, mul_one, positive_square]

theorem mirror_boost8 (a : Fin 3) :
    mirror8 * boost8 a * mirror8 = -boost8 a := by
  unfold boost8
  rw [mul_smul_comm, smul_mul_assoc, mirror8_kronecker_sandwich,
    positive_chirality_sandwich, kronecker_neg_left, smul_neg]

theorem mirror_chiralSpinPlus (a : Fin 3) :
    mirror8 * chiralSpinPlus a * mirror8 = chiralSpinMinus a := by
  unfold chiralSpinPlus chiralSpinMinus
  rw [mirror8_kronecker_sandwich, positive_upperCorner_sandwich]

theorem mirror_chiralSpinMinus (a : Fin 3) :
    mirror8 * chiralSpinMinus a * mirror8 = chiralSpinPlus a := by
  unfold chiralSpinPlus chiralSpinMinus
  rw [mirror8_kronecker_sandwich, positive_lowerCorner_sandwich]

theorem chiralSpinPlus_mul_minus (a b : Fin 3) :
    chiralSpinPlus a * chiralSpinMinus b = 0 := by
  unfold chiralSpinPlus chiralSpinMinus
  rw [← Matrix.mul_kronecker_mul, (corners_orthogonal (A := ℝ)).1,
    Matrix.zero_kronecker]

theorem chiralSpinMinus_mul_plus (a b : Fin 3) :
    chiralSpinMinus a * chiralSpinPlus b = 0 := by
  unfold chiralSpinPlus chiralSpinMinus
  rw [← Matrix.mul_kronecker_mul, (corners_orthogonal (A := ℝ)).2,
    Matrix.zero_kronecker]

theorem chiralSpinPlus_commutator_cyclic (a : Fin 3) :
    chiralSpinPlus a * chiralSpinPlus (a + 1) -
        chiralSpinPlus (a + 1) * chiralSpinPlus a = chiralSpinPlus (a + 2) := by
  simp only [chiralSpinPlus, ← Matrix.mul_kronecker_mul, upperCorner_idempotent,
    ← kronecker_sub_right, rotation_commutator_cyclic]

theorem chiralSpinMinus_commutator_cyclic (a : Fin 3) :
    chiralSpinMinus a * chiralSpinMinus (a + 1) -
        chiralSpinMinus (a + 1) * chiralSpinMinus a = chiralSpinMinus (a + 2) := by
  simp only [chiralSpinMinus, ← Matrix.mul_kronecker_mul, lowerCorner_idempotent,
    ← kronecker_sub_right, rotation_commutator_cyclic]

theorem rotation8_commutator_cyclic (a : Fin 3) :
    rotation8 a * rotation8 (a + 1) - rotation8 (a + 1) * rotation8 a =
      rotation8 (a + 2) := by
  simp only [rotation8, ← Matrix.mul_kronecker_mul, one_mul,
    ← kronecker_sub_right, rotation_commutator_cyclic]

theorem rotation8_boost8_commutator_cyclic (a : Fin 3) :
    rotation8 a * boost8 (a + 1) - boost8 (a + 1) * rotation8 a = boost8 (a + 2) := by
  simp only [rotation8, boost8, mul_smul_comm, smul_mul_assoc,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one, ← smul_sub,
    ← kronecker_sub_right, rotation_sigma_commutator_cyclic]

theorem boost8_commutator_cyclic (a : Fin 3) :
    boost8 a * boost8 (a + 1) - boost8 (a + 1) * boost8 a = -rotation8 (a + 2) := by
  simp only [boost8, smul_mul_smul, ← Matrix.mul_kronecker_mul, chirality_square]
  rw [← smul_sub, ← kronecker_sub_right, sigma_commutator_cyclic,
    Matrix.kronecker_smul, smul_smul]
  norm_num [rotation8]

theorem rotation8_transpose (a : Fin 3) : (rotation8 a)ᵀ = -rotation8 a := by
  simp only [rotation8, kronecker_transpose, Matrix.transpose_one,
    rotation_transpose, kronecker_neg_right]

theorem boost8_transpose (a : Fin 3) : (boost8 a)ᵀ = boost8 a := by
  simp only [boost8, Matrix.transpose_smul, kronecker_transpose,
    chirality_transpose, sigma_transpose]

/-- Infinitesimal preservation of the cross-sheet mirror metric by rotations. -/
theorem rotation8_krein_infinitesimal (a : Fin 3) :
    (rotation8 a)ᵀ * mirror8 + mirror8 * rotation8 a = 0 := by
  rw [rotation8_transpose]
  simp only [rotation8, mirror8, neg_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, neg_add_cancel]

/-- Infinitesimal preservation of the same metric by the symmetric boosts. -/
theorem boost8_krein_infinitesimal (a : Fin 3) :
    (boost8 a)ᵀ * mirror8 + mirror8 * boost8 a = 0 := by
  rw [boost8_transpose]
  simp only [boost8, mirror8, smul_mul_assoc, mul_smul_comm,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one, ← smul_add,
    ← Matrix.add_kronecker, chirality_positive_anticommutator,
    Matrix.zero_kronecker, smul_zero]

private theorem offDiagonal_square (A B : Mat4R) :
    ((upperLadder : Mat2R) ⊗ₖ A + (lowerLadder : Mat2R) ⊗ₖ B) *
        ((upperLadder : Mat2R) ⊗ₖ A + (lowerLadder : Mat2R) ⊗ₖ B) =
      (upperCorner : Mat2R) ⊗ₖ (A * B) + (lowerCorner : Mat2R) ⊗ₖ (B * A) := by
  simp only [add_mul, mul_add, ← Matrix.mul_kronecker_mul,
    upperLadder_square, lowerLadder_square,
    upperLadder_mul_lowerLadder, lowerLadder_mul_upperLadder,
    Matrix.zero_kronecker, zero_add, add_zero]
  exact add_comm _ _

/-- The Weyl square is the real Minkowski quadratic form on all coordinates. -/
theorem weylDirac8_square (t x y z : ℝ) :
    weylDirac8 t x y z * weylDirac8 t x y z =
      (t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) • (1 : Mat8R) := by
  unfold weylDirac8
  rw [offDiagonal_square, solder_mul_conjugate, solderConjugate_mul_solder,
    ← Matrix.add_kronecker, corner_sum, Matrix.kronecker_smul,
    Matrix.one_kronecker_one]

private theorem offDiagonal_time_spatial (t : ℝ) (A : Mat4R) :
    (upperLadder : Mat2R) ⊗ₖ (t • (1 : Mat4R) + A) +
        (lowerLadder : Mat2R) ⊗ₖ (t • (1 : Mat4R) - A) =
      t • ((positive : Mat2R) ⊗ₖ (1 : Mat4R)) + (negative : Mat2R) ⊗ₖ A := by
  ext ⟨i, r⟩ ⟨j, s⟩
  fin_cases i <;> fin_cases j <;>
    simp [upperLadder, lowerLadder, positive, negative]
  all_goals ring

/-- Time is carried by the sheet exchange and space by the negative-square atom. -/
theorem weylDirac8_one_plus_three (t x y z : ℝ) :
    weylDirac8 t x y z = t • mirror8 +
      (negative : Mat2R) ⊗ₖ (x • sigma 0 + y • sigma 1 + z • sigma 2) := by
  have hs : solder t x y z =
      t • (1 : Mat4R) + (x • sigma 0 + y • sigma 1 + z • sigma 2) := by
    unfold solder
    abel
  have hc : solderConjugate t x y z =
      t • (1 : Mat4R) - (x • sigma 0 + y • sigma 1 + z • sigma 2) := by
    simp only [solderConjugate, solder, neg_smul, sub_eq_add_neg, neg_add]
    abel
  rw [weylDirac8, hs, hc, offDiagonal_time_spatial]
  rfl

private theorem solderConjugate_transpose (t x y z : ℝ) :
    (solderConjugate t x y z)ᵀ = solderConjugate t x y z := by
  exact solder_transpose t (-x) (-y) (-z)

/-- The off-diagonal Weyl matrix is self-adjoint for the cross-sheet metric. -/
theorem weylDirac8_krein_selfadjoint (t x y z : ℝ) :
    (weylDirac8 t x y z)ᵀ * mirror8 = mirror8 * weylDirac8 t x y z := by
  simp only [weylDirac8, mirror8, Matrix.transpose_add, kronecker_transpose,
    solder_transpose, solderConjugate_transpose, add_mul, mul_add,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one,
    upperLadder_transpose_mul_positive, lowerLadder_transpose_mul_positive]

theorem mirror8_weylDirac8_transpose (t x y z : ℝ) :
    mirror8 * (weylDirac8 t x y z)ᵀ * mirror8 = weylDirac8 t x y z := by
  rw [mul_assoc, weylDirac8_krein_selfadjoint, ← mul_assoc,
    mirror8_square, one_mul]

end InfoGeometry.Clifford.RealChiralWeyl
