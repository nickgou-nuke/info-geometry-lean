/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SplitAtomDoubling.Basic

/-!
# Klein parity and the split matrix atom

The coefficient ring is arbitrary and may be noncommutative. The existing
`twisted` map is the odd insertion, not an algebra homomorphism. A genuine
graded-algebra insertion must use `repeated` on even coefficients.

The reconstruction theorem is an integral identity for `M + M`. Recovering
`M` from it requires division by two; no such assumption is made here.
-/

namespace InfoGeometry.Clifford.SplitAtomDoubling

variable {A : Type*} [Ring A]

/-- The grading involution, with diagonal entries `1` and `-1`. -/
def chirality : Block2 A := twisted 1

/-- The negative-square seed in the orientation `[[0,-1],[1,0]]`. -/
def omega : Block2 A := -negative

/-- The upper and lower Peirce idempotents. -/
def upperCorner : Block2 A := !![1, 0; 0, 0]
def lowerCorner : Block2 A := !![0, 0; 0, 1]

/-- The two off-diagonal matrix units. -/
def upperLadder : Block2 A := !![0, 1; 0, 0]
def lowerLadder : Block2 A := !![0, 0; 1, 0]

@[simp] theorem repeated_zero : repeated (0 : A) = 0 := repeatedHom.map_zero
@[simp] theorem repeated_one : repeated (1 : A) = 1 := repeatedHom.map_one
@[simp] theorem repeated_neg (a : A) : repeated (-a) = -repeated a :=
  repeatedHom.map_neg a

@[simp] theorem chirality_square : (chirality : Block2 A) * chirality = 1 := by
  simpa [chirality] using twisted_mul (1 : A) 1

@[simp] theorem omega_square : (omega : Block2 A) * omega = -1 := by
  simp [omega]

theorem positive_mul_omega : (positive : Block2 A) * omega = chirality := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, omega, negative, chirality, twisted, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem twisted_eq_repeated_mul_chirality (a : A) :
    twisted a = repeated a * chirality := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, repeated, chirality, Matrix.mul_apply, Fin.sum_univ_two]

theorem repeated_commute_positive (a : A) : Commute (repeated a) positive := by
  change repeated a * positive = positive * repeated a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, repeated, Matrix.mul_apply, Fin.sum_univ_two]

theorem repeated_commute_negative (a : A) : Commute (repeated a) negative := by
  change repeated a * negative = negative * repeated a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negative, repeated, Matrix.mul_apply, Fin.sum_univ_two]

theorem twisted_omega_anticommutator (a : A) :
    twisted a * omega + omega * twisted a = 0 := by
  rw [omega, mul_neg, neg_mul, ← neg_add, twisted_negative_anticommutator, neg_zero]

theorem positive_omega_anticommutator :
    (positive : Block2 A) * omega + omega * positive = 0 := by
  rw [omega, mul_neg, neg_mul, ← neg_add, head_anticommutator, neg_zero]

theorem chirality_commute_twisted (a : A) : Commute chirality (twisted a) := by
  change twisted (1 : A) * twisted a = twisted a * twisted 1
  rw [twisted_mul, twisted_mul, one_mul, mul_one]

theorem chirality_positive_anticommutator :
    (chirality : Block2 A) * positive + positive * chirality = 0 :=
  twisted_positive_anticommutator 1

theorem chirality_omega_anticommutator :
    (chirality : Block2 A) * omega + omega * chirality = 0 :=
  twisted_omega_anticommutator 1

theorem upperCorner_idempotent : (upperCorner : Block2 A) * upperCorner = upperCorner := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperCorner, Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerCorner_idempotent : (lowerCorner : Block2 A) * lowerCorner = lowerCorner := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerCorner, Matrix.mul_apply, Fin.sum_univ_two]

theorem corner_sum : (upperCorner : Block2 A) + lowerCorner = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperCorner, lowerCorner]

theorem corner_difference : (upperCorner : Block2 A) - lowerCorner = chirality := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperCorner, lowerCorner, chirality, twisted]

theorem corners_orthogonal :
    (upperCorner : Block2 A) * lowerCorner = 0 ∧
      (lowerCorner : Block2 A) * upperCorner = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [upperCorner, lowerCorner, Matrix.mul_apply, Fin.sum_univ_two]

theorem upperLadder_peirce :
    (upperLadder : Block2 A) = upperCorner * positive * lowerCorner := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperLadder, upperCorner, lowerCorner, positive, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem lowerLadder_peirce :
    (lowerLadder : Block2 A) = lowerCorner * positive * upperCorner := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerLadder, upperCorner, lowerCorner, positive, Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp] theorem upperLadder_square : (upperLadder : Block2 A) * upperLadder = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperLadder, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem lowerLadder_square : (lowerLadder : Block2 A) * lowerLadder = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerLadder, Matrix.mul_apply, Fin.sum_univ_two]

theorem upperLadder_mul_lowerLadder :
    (upperLadder : Block2 A) * lowerLadder = upperCorner := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperLadder, lowerLadder, upperCorner, Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerLadder_mul_upperLadder :
    (lowerLadder : Block2 A) * upperLadder = lowerCorner := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperLadder, lowerLadder, lowerCorner, Matrix.mul_apply, Fin.sum_univ_two]

theorem ladder_sum : (upperLadder : Block2 A) + lowerLadder = positive := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperLadder, lowerLadder, positive]

theorem ladder_difference : (lowerLadder : Block2 A) - upperLadder = omega := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperLadder, lowerLadder, omega, negative]

theorem ladder_anticommutator :
    (upperLadder : Block2 A) * lowerLadder + lowerLadder * upperLadder = 1 := by
  rw [upperLadder_mul_lowerLadder, lowerLadder_mul_upperLadder, corner_sum]

theorem ladder_commutator :
    (upperLadder : Block2 A) * lowerLadder - lowerLadder * upperLadder = chirality := by
  rw [upperLadder_mul_lowerLadder, lowerLadder_mul_upperLadder, corner_difference]

theorem twisted_upperLadder_anticommutator (a : A) :
    twisted a * upperLadder + upperLadder * twisted a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, upperLadder]

theorem twisted_lowerLadder_anticommutator (a : A) :
    twisted a * lowerLadder + lowerLadder * twisted a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, lowerLadder]

/-- Parity-labelled insertion: a multiplication law, not a grading on an
otherwise ungraded coefficient ring. -/
def parityInsert (p : Bool) (a : A) : Block2 A :=
  if p then twisted a else repeated a

theorem parityInsert_mul (p q : Bool) (a b : A) :
    parityInsert p a * parityInsert q b = parityInsert (Bool.xor p q) (a * b) := by
  cases p <;> cases q <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [parityInsert, twisted, repeated, Matrix.mul_apply, Fin.sum_univ_two]

/-- A corner and its conjugate give the odd coefficient insertion. -/
def kleinFiberLift (M : Block2 A) : Block2 A :=
  upperCorner * M * upperCorner - positive * upperCorner * M * upperCorner * positive

theorem kleinFiberLift_eq_twisted (M : Block2 A) :
    kleinFiberLift M = twisted (M 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kleinFiberLift, upperCorner, positive, twisted, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Integral reconstruction. Its right-hand side deliberately retains the
factor two, including in characteristic two. -/
theorem klein_reconstruction (M : Block2 A) :
    kleinFiberLift (M - positive * M * positive) +
      kleinFiberLift (M + positive * M * positive) * chirality -
      kleinFiberLift (positive * M - M * positive) * positive -
      kleinFiberLift (M * positive + positive * M) * omega = M + M := by
  simp only [kleinFiberLift_eq_twisted]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, omega, negative, chirality, twisted, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> noncomm_ring

end InfoGeometry.Clifford.SplitAtomDoubling
