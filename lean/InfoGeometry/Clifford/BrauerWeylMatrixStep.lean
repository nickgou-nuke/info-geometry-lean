/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NoncommRing

/-!
# The noncommutative Brauer–Weyl matrix step

This file proves finite matrix identities for the Klein twist over an
arbitrary associative ring, including recursively nested matrix stages and
the full finite-stage creation/annihilation CAR.  It
deliberately distinguishes these identities from an abstract
Clifford-algebra equivalence or a general graded tensor universal property.
The two-stage theorem is a statement in the literal nested carrier
`M₂(M₂(B))`.
-/

namespace InfoGeometry.Clifford.BrauerWeylMatrixStep

universe u

open Matrix

variable {A : Type*} [Ring A]

abbrev Op₂ (A : Type*) := Matrix (Fin 2) (Fin 2) A

def chirality : Op₂ A := !![1, 0; 0, -1]
def shift : Op₂ A := !![0, 1; 1, 0]
def rotation : Op₂ A := !![0, -1; 1, 0]
def pPlus : Op₂ A := !![1, 0; 0, 0]
def pMinus : Op₂ A := !![0, 0; 0, 1]

def diagonalLift (x : A) : Op₂ A := !![x, 0; 0, x]
def kleinTwist (x : A) : Op₂ A := !![x, 0; 0, -x]
def create : Op₂ A := !![0, 1; 0, 0]
def annihilate : Op₂ A := !![0, 0; 1, 0]

theorem chirality_sq : (chirality : Op₂ A) * chirality = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chirality, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem shift_sq : (shift : Op₂ A) * shift = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [shift, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem rotation_sq : (rotation : Op₂ A) * rotation = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem shift_rotation_eq_chirality : (shift : Op₂ A) * rotation = chirality := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [shift, rotation, chirality, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem rotation_shift_eq_neg_chirality : (rotation : Op₂ A) * shift = -chirality := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [shift, rotation, chirality, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem chirality_anticomm_shift : (chirality : Op₂ A) * shift + shift * chirality = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chirality, shift, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem chirality_anticomm_rotation :
    (chirality : Op₂ A) * rotation + rotation * chirality = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chirality, rotation, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem shift_anticomm_rotation : (shift : Op₂ A) * rotation + rotation * shift = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [shift, rotation, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

/-- The matrix operator algebra is noncommutative whenever the coefficient
ring is nontrivial: the two ordered products differ in their upper-right
matrix coefficient. -/
theorem pPlus_shift_noncommute [Nontrivial A] :
    (pPlus : Op₂ A) * shift ≠ shift * pPlus := by
  intro h
  have h01 := congrArg (fun M : Op₂ A => M 0 1) h
  have hl : ((pPlus : Op₂ A) * (shift : Op₂ A)) 0 1 = (1 : A) := by
    simp [pPlus, shift, Matrix.mul_apply, Fin.sum_univ_two]
  have hr : ((shift : Op₂ A) * (pPlus : Op₂ A)) 0 1 = (0 : A) := by
    simp [pPlus, shift, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hl, hr] at h01
  exact one_ne_zero h01

theorem diagonalLift_mul (x y : A) : diagonalLift x * diagonalLift y = diagonalLift (x * y) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalLift, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem diagonalLift_one : diagonalLift (1 : A) = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagonalLift]

theorem diagonalLift_zero : diagonalLift (0 : A) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagonalLift]

theorem diagonalLift_add (x y : A) :
    diagonalLift (x + y) = diagonalLift x + diagonalLift y := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalLift]

/-- Diagonal coefficients commute with the scalar shift matrix. -/
theorem diagonalLift_comm_shift (x : A) :
    diagonalLift x * shift = shift * diagonalLift x := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalLift, shift, Matrix.mul_apply, Fin.sum_univ_two]

/-- A diagonal coefficient commutes with a Klein-twisted operator exactly
when the coefficient commutes with the operator being twisted. -/
theorem diagonalLift_comm_kleinTwist_of (x y : A) (h : x * y = y * x) :
    diagonalLift x * kleinTwist y = kleinTwist y * diagonalLift x := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalLift, kleinTwist, Matrix.mul_apply, Fin.sum_univ_two, h]

/-- For a diagonal coefficient lift, commutation with a Klein-twisted
operator is equivalent to commutation of the underlying ordered
coefficients. No centrality of either coefficient is assumed. -/
theorem diagonalLift_comm_kleinTwist_iff (x y : A) :
    diagonalLift x * kleinTwist y = kleinTwist y * diagonalLift x ↔ x * y = y * x := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Op₂ A => M 0 0) h
    simpa [diagonalLift, kleinTwist, Matrix.mul_apply, Fin.sum_univ_two] using h00
  · exact diagonalLift_comm_kleinTwist_of x y

/-- Diagonal coefficients commute with the scalar rotation matrix. -/
theorem diagonalLift_comm_rotation (x : A) :
    diagonalLift x * rotation = rotation * diagonalLift x := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalLift, rotation, Matrix.mul_apply, Fin.sum_univ_two]

/-- Diagonal coefficients commute with the scalar creation matrix unit. -/
theorem diagonalLift_comm_create (x : A) :
    diagonalLift x * create = create * diagonalLift x := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalLift, create, Matrix.mul_apply, Fin.sum_univ_two]

/-- Diagonal coefficients commute with the scalar annihilation matrix unit. -/
theorem diagonalLift_comm_annihilate (x : A) :
    diagonalLift x * annihilate = annihilate * diagonalLift x := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalLift, annihilate, Matrix.mul_apply, Fin.sum_univ_two]

/-- The simultaneous commutant of the two matrix units `create` and
`annihilate` consists exactly of the equal-entry coefficient lifts. This
uses both ordered operator equations and is valid over every ring. -/
theorem commutant_create_annihilate_eq_diagonalLift (M : Op₂ A) :
    (M * create = create * M ∧ M * annihilate = annihilate * M) ↔
      ∃ a : A, M = diagonalLift a := by
  constructor
  · rintro ⟨hc, ha⟩
    have hc00 := congrArg (fun N : Op₂ A => N 0 0) hc
    have hc01 := congrArg (fun N : Op₂ A => N 0 1) hc
    have ha00 := congrArg (fun N : Op₂ A => N 0 0) ha
    have h10 : M 1 0 = 0 := by
      simpa [create, Matrix.mul_apply, Fin.sum_univ_two] using hc00.symm
    have h01 : M 0 1 = 0 := by
      simpa [annihilate, Matrix.mul_apply, Fin.sum_univ_two] using ha00
    have hdiag : M 0 0 = M 1 1 := by
      simpa [create, Matrix.mul_apply, Fin.sum_univ_two] using hc01
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · simpa [diagonalLift] using h01
    · simpa [diagonalLift] using h10
    · simpa [diagonalLift] using hdiag.symm
  · rintro ⟨a, rfl⟩
    exact ⟨diagonalLift_comm_create a, diagonalLift_comm_annihilate a⟩

/-- The diagonal lift is a unital ring homomorphism. -/
def diagonalLiftHom : A →+* Op₂ A where
  toFun := diagonalLift
  map_one' := diagonalLift_one
  map_mul' := fun x y => (diagonalLift_mul x y).symm
  map_zero' := diagonalLift_zero
  map_add' := diagonalLift_add

theorem diagonalLift_neg_one : diagonalLift (-1 : A) = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagonalLift]

theorem kleinTwist_eq_diagonalLift_mul_chirality (x : A) :
    kleinTwist x = diagonalLift x * chirality := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, diagonalLift, chirality, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

/-- The ordered product of two Klein twists is the diagonal lift of the
ordered product in `A`; no commutativity assumption is used. -/
theorem kleinTwist_mul (x y : A) :
    kleinTwist x * kleinTwist y = diagonalLift (x * y) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, diagonalLift, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem kleinTwist_anticomm_shift (x : A) :
    kleinTwist x * shift + shift * kleinTwist x = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, shift, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem kleinTwist_anticomm_rotation (x : A) :
    kleinTwist x * rotation + rotation * kleinTwist x = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, rotation, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem create_eq_pPlus_shift_pMinus :
    (create : Op₂ A) = pPlus * shift * pMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [create, pPlus, pMinus, shift, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem annihilate_eq_pMinus_shift_pPlus :
    (annihilate : Op₂ A) = pMinus * shift * pPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [annihilate, pPlus, pMinus, shift, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem witt_ladder_car :
    (create : Op₂ A) * create = 0 ∧ (annihilate : Op₂ A) * annihilate = 0 ∧
      (create : Op₂ A) * annihilate + annihilate * create = 1 ∧
      (create : Op₂ A) * annihilate - annihilate * create = chirality := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [create, annihilate, chirality, Matrix.mul_apply,
        Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem kleinTwist_anticomm_create (x : A) :
    kleinTwist x * create + create * kleinTwist x = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, create, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem kleinTwist_anticomm_annihilate (x : A) :
    kleinTwist x * annihilate + annihilate * kleinTwist x = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, annihilate, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

/-- Klein twisting transports an anticommuting ordered pair to an
anticommuting pair of operators in the next matrix stage. -/
theorem kleinTwist_anticomm_of {x y : A} (h : x * y + y * x = 0) :
    kleinTwist x * kleinTwist y + kleinTwist y * kleinTwist x = 0 := by
  rw [kleinTwist_mul, kleinTwist_mul, ← diagonalLift_add, h, diagonalLift_zero]

theorem kleinTwist_anticomm_eq (x y : A) :
    kleinTwist x * kleinTwist y + kleinTwist y * kleinTwist x =
      diagonalLift (x * y + y * x) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kleinTwist, diagonalLift, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Klein twisting also preserves square-zero operators. -/
theorem kleinTwist_sq_zero {x : A} (h : x * x = 0) :
    kleinTwist x * kleinTwist x = 0 := by
  rw [kleinTwist_mul, h, diagonalLift_zero]

section TwoStage

variable {B : Type u} [Ring B]

abbrev NestedOp₂ (B : Type*) := Op₂ (Op₂ B)

def outerShift : NestedOp₂ B := shift
def outerRotation : NestedOp₂ B := rotation
def outerKlein (x : Op₂ B) : NestedOp₂ B := kleinTwist x

/-- The four recursively twisted generators in the literal nested matrix
algebra.  Their signature is `(+,-,+,-)` and they anticommute pairwise. -/
theorem nested_cl22_relations :
    (outerShift : NestedOp₂ B) * outerShift = 1 ∧
    (outerRotation : NestedOp₂ B) * outerRotation = -1 ∧
    outerKlein (shift : Op₂ B) * outerKlein shift = 1 ∧
    outerKlein (rotation : Op₂ B) * outerKlein rotation = -1 ∧
    (outerShift : NestedOp₂ B) * outerRotation + outerRotation * outerShift = 0 ∧
    outerKlein (shift : Op₂ B) * outerShift + outerShift * outerKlein shift = 0 ∧
    outerKlein (rotation : Op₂ B) * outerShift + outerShift * outerKlein rotation = 0 ∧
    outerKlein (shift : Op₂ B) * outerRotation + outerRotation * outerKlein shift = 0 ∧
    outerKlein (rotation : Op₂ B) * outerRotation + outerRotation * outerKlein rotation = 0 ∧
    outerKlein (shift : Op₂ B) * outerKlein rotation +
      outerKlein rotation * outerKlein shift = 0 := by
  refine ⟨shift_sq, rotation_sq, ?_, ?_, shift_anticomm_rotation,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa [outerKlein, shift_sq, diagonalLift_one] using
      (kleinTwist_mul (A := Op₂ B) (shift : Op₂ B) shift)
  · simpa [outerKlein, rotation_sq, diagonalLift_neg_one] using
      (kleinTwist_mul (A := Op₂ B) (rotation : Op₂ B) rotation)
  · exact kleinTwist_anticomm_shift (A := Op₂ B) (shift : Op₂ B)
  · exact kleinTwist_anticomm_shift (A := Op₂ B) (rotation : Op₂ B)
  · exact kleinTwist_anticomm_rotation (A := Op₂ B) (shift : Op₂ B)
  · simpa [outerRotation, outerKlein, add_comm] using
      (kleinTwist_anticomm_rotation (A := Op₂ B) (rotation : Op₂ B))
  · have h₁ := kleinTwist_mul (A := Op₂ B) (shift : Op₂ B) rotation
    have h₂ := kleinTwist_mul (A := Op₂ B) (rotation : Op₂ B) shift
    change kleinTwist (shift : Op₂ B) * kleinTwist rotation +
      kleinTwist rotation * kleinTwist shift = 0
    rw [h₁, h₂, shift_rotation_eq_chirality, rotation_shift_eq_neg_chirality]
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagonalLift]

end TwoStage

section QuaternionRotors

variable {B : Type u} [Ring B]

/-- In any noncommutative operator ring, two anticommuting generators whose
squares are `-1` determine the third quaternion unit by ordered multiplication. -/
theorem skew_pair_quaternion_relations {e f : B}
    (he : e * e = -1) (hf : f * f = -1) (hef : e * f + f * e = 0) :
    let g := e * f
    g * g = -1 ∧
      (e * f - f * e = 2 * g) ∧
      (f * g - g * f = 2 * e) ∧
      (g * e - e * g = 2 * f) := by
  have hfe : f * e = -(e * f) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hef)
  dsimp
  constructor
  · calc
      e * f * (e * f) = e * (f * e) * f := by noncomm_ring
      _ = e * (-(e * f)) * f := by rw [hfe]
      _ = -((e * e) * (f * f)) := by noncomm_ring
      _ = -1 := by rw [he, hf]; norm_num
  constructor
  · rw [hfe]
    noncomm_ring
  constructor
  · calc
      f * (e * f) - (e * f) * f = (f * e) * f - e * (f * f) := by noncomm_ring
      _ = (-(e * f)) * f - e * (-1) := by rw [hfe, hf]
      _ = e + e := by simp [mul_assoc, hf]
      _ = 2 * e := (two_mul e).symm
  · calc
      (e * f) * e - e * (e * f) = e * (f * e) - (e * e) * f := by noncomm_ring
      _ = e * (-(e * f)) - (-1) * f := by rw [hfe, he]
      _ = 2 * f := by
        calc
          e * (-(e * f)) - (-1) * f = f + f := by rw [mul_neg, ← mul_assoc, he]; simp
          _ = 2 * f := (two_mul f).symm

/-- The algebraic Cayley rotor `1+e` sends the orthogonal quaternion unit
`f` to twice the ordered third unit `e*f`. No division or commutativity is
used. -/
theorem cayley_rotor_quaternion_frame {e f : B}
    (he : e * e = -1) (hef : e * f + f * e = 0) :
    (1 + e) * f * (1 - e) = 2 * (e * f) := by
  have hfe : f * e = -(e * f) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hef)
  calc
    (1 + e) * f * (1 - e) = f - f * e + e * f - e * f * e := by noncomm_ring
    _ = f - (-(e * f)) + e * f - e * f * e := by rw [hfe]
    _ = f + e * f + e * f - f := by
      have hefe : e * f * e = f := by
        calc
          e * f * e = e * (f * e) := by noncomm_ring
          _ = e * (-(e * f)) := by rw [hfe]
          _ = f := by calc
            e * (-(e * f)) = -(e * e * f) := by noncomm_ring
            _ = f := by rw [he]; simp
      rw [hefe]
      noncomm_ring
    _ = 2 * (e * f) := by
      have hcancel : f + e * f + e * f - f = e * f + e * f := by abel
      rw [hcancel]
      exact (two_mul (e * f)).symm

/-- The two algebraic Cayley rotors retain the ordered commutator of their
axes; in particular this result does not assume that the coefficient ring is
commutative. -/
theorem cayley_rotor_commutator {e f : B}
    (hef : e * f + f * e = 0) :
    (1 + e) * (1 + f) - (1 + f) * (1 + e) = 2 * (e * f) := by
  have hfe : f * e = -(e * f) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hef)
  calc
    (1 + e) * (1 + f) - (1 + f) * (1 + e)
        = e * f - f * e := by noncomm_ring
    _ = 2 * (e * f) := by
      rw [hfe]
      calc
        e * f - -(e * f) = e * f + e * f := by abel
        _ = 2 * (e * f) := (two_mul (e * f)).symm

/-- Skew-involutive anticommuting generators give an Artin braid relation
for the algebraic Cayley rotors `1 + e` and `1 + f`. Both triple products
reduce to the same ordered sum; no scalar commutativity is assumed. -/
theorem cayley_rotors_artin_braid {e f : B}
    (he : e * e = -1) (hf : f * f = -1)
    (hef : e * f + f * e = 0) :
    (1 + e) * (1 + f) * (1 + e) =
      (1 + f) * (1 + e) * (1 + f) := by
  have hleft : (1 + e) * (1 + f) * (1 + e) = 2 * (e + f) := by
    calc
      (1 + e) * (1 + f) * (1 + e) =
          2 * (e + f) + (e * e + 1) * (1 - f) +
            (1 + e) * (e * f + f * e) := by noncomm_ring
      _ = 2 * (e + f) := by rw [he, hef]; noncomm_ring
  have hright : (1 + f) * (1 + e) * (1 + f) = 2 * (f + e) := by
    calc
      (1 + f) * (1 + e) * (1 + f) =
          2 * (f + e) + (f * f + 1) * (1 - e) +
            (1 + f) * (f * e + e * f) := by noncomm_ring
      _ = 2 * (f + e) := by
        have hfe : f * e + e * f = 0 := by simpa [add_comm] using hef
        rw [hf, hfe]
        noncomm_ring
  calc
    (1 + e) * (1 + f) * (1 + e) = 2 * (e + f) := hleft
    _ = 2 * (f + e) := by rw [add_comm]
    _ = (1 + f) * (1 + e) * (1 + f) := hright.symm

/-- Quaternion operators inherited from the two negative-square generators
at the second matrix stage. This is a theorem in `M₂(M₂(B))`, not a scalar
or diagonal model. -/
theorem nested_quaternion_operator_relations :
    let e₁ : NestedOp₂ B := outerRotation
    let e₂ : NestedOp₂ B := outerKlein rotation
    let e₃ : NestedOp₂ B := e₁ * e₂
    e₁ * e₁ = -1 ∧ e₂ * e₂ = -1 ∧ e₃ * e₃ = -1 ∧
      (e₁ * e₂ - e₂ * e₁ = 2 * e₃) ∧
      (e₂ * e₃ - e₃ * e₂ = 2 * e₁) ∧
      (e₃ * e₁ - e₁ * e₃ = 2 * e₂) ∧
      ((1 + e₁) * (1 + e₂) - (1 + e₂) * (1 + e₁) = 2 * e₃) ∧
      (1 + e₁) * e₂ * (1 - e₁) = 2 * e₃ := by
  let e₁ : NestedOp₂ B := outerRotation
  let e₂ : NestedOp₂ B := outerKlein (rotation : Op₂ B)
  have he₁ : e₁ * e₁ = -1 := by simpa [e₁, outerRotation] using
    (rotation_sq (A := Op₂ B))
  have he₂ : e₂ * e₂ = -1 := by
    calc
      e₂ * e₂ = diagonalLift (rotation * rotation) := by
        simp [e₂, outerKlein, kleinTwist_mul]
      _ = -1 := by rw [rotation_sq]; exact diagonalLift_neg_one
  have hanti : e₁ * e₂ + e₂ * e₁ = 0 := by
    simpa [e₁, e₂, outerRotation, outerKlein, add_comm] using
      (kleinTwist_anticomm_rotation (A := Op₂ B) (rotation : Op₂ B))
  have h := skew_pair_quaternion_relations (B := NestedOp₂ B) he₁ he₂ hanti
  rcases h with ⟨he₃, h₁₂, h₂₃, h₃₁⟩
  exact ⟨he₁, he₂, he₃, h₁₂, h₂₃, h₃₁,
    cayley_rotor_commutator hanti,
    cayley_rotor_quaternion_frame he₁ hanti⟩

/-- The concrete quaternion axes in the recursively nested operator algebra
`M₂(M₂(B))` also give an Artin braid representation. This specializes the
general rotor identity to the noncommutative Brauer–Weyl operators. -/
theorem nested_quaternion_artin_braid :
    let e₁ : NestedOp₂ B := outerRotation
    let e₂ : NestedOp₂ B := outerKlein rotation
    (1 + e₁) * (1 + e₂) * (1 + e₁) =
      (1 + e₂) * (1 + e₁) * (1 + e₂) := by
  dsimp
  apply cayley_rotors_artin_braid
  · exact rotation_sq (A := Op₂ B)
  · calc
      kleinTwist (rotation : Op₂ B) * kleinTwist rotation =
          diagonalLift (rotation * rotation) := kleinTwist_mul _ _
      _ = -1 := by rw [rotation_sq]; exact diagonalLift_neg_one
  · simpa [outerRotation, outerKlein, add_comm] using
      (kleinTwist_anticomm_rotation (A := Op₂ B) (rotation : Op₂ B))

end QuaternionRotors

section RecursiveTower

variable {B : Type*} [Ring B]

/-- The recursively nested operator ring with `n` binary matrix layers over
the (possibly noncommutative) coefficient ring `B`. -/
abbrev OperatorStage (B : Type u) : ℕ → Type u
  | 0 => B
  | n + 1 => Op₂ (OperatorStage B n)

instance operatorStageRing (n : ℕ) : Ring (OperatorStage B n) := by
  induction n with
  | zero => change Ring B; exact inferInstance
  | succ n ih =>
      letI : Ring (OperatorStage B n) := ih
      change Ring (Op₂ (OperatorStage B n))
      exact inferInstance

/-- The canonical transition from one finite operator stage to the next.
It repeats an operator in the two outer Peirce blocks, so the coefficient
ring remains the same possibly noncommutative ring `B`. -/
def operatorStageEmbed (n : ℕ) :
    OperatorStage B n →+* OperatorStage B (n + 1) :=
  diagonalLiftHom (A := OperatorStage B n)

/-- The stage transition is faithful: its upper-left operator block recovers
the entire preceding stage. -/
theorem operatorStageEmbed_injective (n : ℕ) :
    Function.Injective (operatorStageEmbed (B := B) n) := by
  intro x y h
  have h₀₀ := congrArg (fun M : Op₂ (OperatorStage B n) => M 0 0) h
  simpa [operatorStageEmbed, diagonalLiftHom, diagonalLift] using h₀₀

/-- The canonical finite jump from stage `n` to stage `n + k`, obtained by
composing the one-step diagonal operator embeddings. -/
def operatorStageEmbedding : (n k : ℕ) →
    OperatorStage B n →+* OperatorStage B (n + k)
  | n, 0 => RingHom.id (OperatorStage B n)
  | n, k + 1 =>
      (operatorStageEmbed (B := B) (n + k)).comp
        (operatorStageEmbedding n k)

/-- Every finite-stage transition is faithful, so no operator is collapsed
when the nested noncommutative matrix tower is enlarged. -/
theorem operatorStageEmbedding_injective (n k : ℕ) :
    Function.Injective (operatorStageEmbedding (B := B) n k) := by
  induction k with
  | zero =>
      intro x y h
      exact h
  | succ k ih =>
      intro x y h
      apply ih
      exact operatorStageEmbed_injective (B := B) (n + k) h

/-- The row/column index for the full matrix algebra represented by a nested
binary operator stage. -/
def OperatorIndex : ℕ → Type
  | 0 => Fin 1
  | n + 1 => Fin 2 × OperatorIndex n

instance operatorIndexFintype (n : ℕ) : Fintype (OperatorIndex n) := by
  induction n with
  | zero => dsimp [OperatorIndex]; infer_instance
  | succ n ih =>
      dsimp [OperatorIndex]
      exact @instFintypeProd (Fin 2) (OperatorIndex n) inferInstance ih

instance operatorIndexDecidableEq (n : ℕ) : DecidableEq (OperatorIndex n) := by
  induction n with
  | zero => dsimp [OperatorIndex]; infer_instance
  | succ n ih =>
      dsimp [OperatorIndex]
      exact @instDecidableEqProd (Fin 2) (OperatorIndex n) inferInstance ih

/-- Flatten a nested layer using Mathlib's matrix-composition ring
equivalence, valid over noncommutative coefficient rings. -/
def flattenMatrixLayer (I : Type*) [Fintype I] :
    Matrix (Fin 2) (Fin 2) (Matrix I I B) ≃+*
      Matrix (Fin 2 × I) (Fin 2 × I) B :=
  Matrix.compRingEquiv (Fin 2) I B

/-- Identify the coefficient ring with its one-by-one matrix operator algebra. -/
def flattenOne : B ≃+* Matrix (Fin 1) (Fin 1) B :=
  (Matrix.uniqueRingEquiv (m := Fin 1) (A := B)).symm

/-- Flatten all recursive matrix layers into a single full matrix algebra over
the original, possibly noncommutative, coefficient ring. -/
def flattenOperatorStage : (n : ℕ) → OperatorStage B n ≃+*
    Matrix (OperatorIndex n) (OperatorIndex n) B
  | 0 => flattenOne
  | n + 1 =>
      ((flattenOperatorStage n).mapMatrix).trans (flattenMatrixLayer (OperatorIndex n))

/-- Entrywise form of the recursive full-matrix identification. -/
@[simp] theorem flattenOperatorStage_succ_apply (n : ℕ)
    (M : OperatorStage B (n + 1)) (i j : Fin 2)
    (a b : OperatorIndex n) :
    flattenOperatorStage (B := B) (n + 1) M (i, a) (j, b) =
      flattenOperatorStage (B := B) n (M i j) a b := rfl

/-- Under the recursive full-matrix identification, the stage transition
acts by the exact block-diagonal formula: entries are copied within each
outer sector and vanish between the two sectors. -/
theorem flattenOperatorStage_operatorStageEmbed_apply (n : ℕ)
    (M : OperatorStage B n) (i j : Fin 2) (a b : OperatorIndex n) :
    flattenOperatorStage (B := B) (n + 1) (operatorStageEmbed (B := B) n M)
        (i, a) (j, b) =
      if i = j then flattenOperatorStage (B := B) n M a b else 0 := by
  rw [flattenOperatorStage_succ_apply]
  fin_cases i <;> fin_cases j <;>
    simp [operatorStageEmbed, diagonalLiftHom, diagonalLift]

/-- The next transition after any finite jump has the same exact block
diagonal action after flattening; the copied diagonal block is the already
embedded operator at stage `n + k`. -/
theorem flattenOperatorStageEmbedding_succ_apply (n k : ℕ)
    (M : OperatorStage B n) (i j : Fin 2)
    (a b : OperatorIndex (n + k)) :
    flattenOperatorStage (B := B) (n + (k + 1))
        (operatorStageEmbedding (B := B) n (k + 1) M)
        (i, a) (j, b) =
      if i = j then
        flattenOperatorStage (B := B) (n + k)
          (operatorStageEmbedding (B := B) n k M) a b
      else 0 := by
  change flattenOperatorStage (B := B) ((n + k) + 1)
      (operatorStageEmbedding (B := B) n (k + 1) M) (i, a) (j, b) = _
  rw [flattenOperatorStage_succ_apply]
  fin_cases i <;> fin_cases j <;>
    simp [operatorStageEmbedding, operatorStageEmbed, diagonalLiftHom,
      diagonalLift]

/-- The full operator index has exactly the expected dimension at every
finite depth. -/
theorem operatorIndex_card_pow_two (n : ℕ) :
    Fintype.card (OperatorIndex n) = 2 ^ n := by
  induction n with
  | zero => simp [OperatorIndex]
  | succ n ih =>
      simp [OperatorIndex, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

/-- A finite indexing equivalence from the recursively structured tensor
index to the standard `Fin (2^n)` operator index. -/
noncomputable def operatorIndexEquivFin (n : ℕ) :
    OperatorIndex n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (operatorIndex_card_pow_two n)

/-- **Full-matrix realization of every nested operator stage.** For every
finite depth and every possibly noncommutative coefficient ring, the
recursively nested binary matrix carrier is ring-isomorphic to the full
`2^n × 2^n` matrix algebra over that same ring. -/
noncomputable def operatorStageFinMatrixEquiv (n : ℕ) :
    OperatorStage B n ≃+* Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B :=
  (flattenOperatorStage (B := B) n).trans
    (Matrix.reindexRingEquiv B (operatorIndexEquivFin n))

/-- Canonical unital inclusion of the coefficient ring into every nested
matrix stage, acting diagonally at each added operator level. -/
def coefficientMap : (n : ℕ) → B →+* OperatorStage B n
  | 0 => RingHom.id B
  | n + 1 => (diagonalLiftHom (A := OperatorStage B n)).comp (coefficientMap n)

/-- The coefficient inclusion is faithful at every finite tower depth. -/
theorem coefficientMap_injective (n : ℕ) :
    Function.Injective (coefficientMap (B := B) n) := by
  induction n with
  | zero => intro x y h; exact h
  | succ n ih =>
      intro x y h
      simp only [coefficientMap, RingHom.comp_apply] at h
      apply ih
      have h₀ := congrArg (fun M : Op₂ (OperatorStage B n) => M 0 0) h
      simpa [diagonalLiftHom, diagonalLift] using h₀

/-- Positive-square Jordan--Wigner generators.  Each new outer site is the
matrix shift; every older generator is Klein-twisted into the new stage. -/
def jwPlus : (n : ℕ) → Fin n → OperatorStage B n
  | 0, i => Fin.elim0 i
  | n + 1, i =>
      if h : (i : ℕ) < n then
        kleinTwist (jwPlus n ⟨i, h⟩)
      else
        shift

/-- Negative-square Jordan--Wigner generators, using the same ordered tower
and the skew outer rotation at each new site. -/
def jwMinus : (n : ℕ) → Fin n → OperatorStage B n
  | 0, i => Fin.elim0 i
  | n + 1, i =>
      if h : (i : ℕ) < n then
        kleinTwist (jwMinus n ⟨i, h⟩)
      else
        rotation

@[simp] theorem jwPlus_castSucc (n : ℕ) (i : Fin n) :
    jwPlus (B := B) (n + 1) i.castSucc = kleinTwist (jwPlus n i) := by
  have h : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n := by
    simpa using i.isLt
  simp [jwPlus, h]

@[simp] theorem jwPlus_last (n : ℕ) :
    jwPlus (B := B) (n + 1) (Fin.last n) = shift := by
  simp [jwPlus]

@[simp] theorem jwMinus_castSucc (n : ℕ) (i : Fin n) :
    jwMinus (B := B) (n + 1) i.castSucc = kleinTwist (jwMinus n i) := by
  have h : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n := by
    simpa using i.isLt
  simp [jwMinus, h]

@[simp] theorem jwMinus_last (n : ℕ) :
    jwMinus (B := B) (n + 1) (Fin.last n) = rotation := by
  simp [jwMinus]

/-- Coefficients embedded from the base ring commute with every positive
Jordan--Wigner generator at every finite depth. -/
theorem coefficientMap_comm_jwPlus : ∀ (n : ℕ) (i : Fin n) (b : B),
    coefficientMap (B := B) n b * jwPlus n i =
      jwPlus n i * coefficientMap (B := B) n b := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i b
      cases i using Fin.lastCases with
      | last =>
          rw [jwPlus_last, coefficientMap, RingHom.comp_apply]
          exact diagonalLift_comm_shift _
      | cast i =>
          rw [jwPlus_castSucc, coefficientMap, RingHom.comp_apply]
          exact diagonalLift_comm_kleinTwist_of _ _ (ih i b)

/-- Coefficients embedded from the base ring commute with every negative
Jordan--Wigner generator at every finite depth. -/
theorem coefficientMap_comm_jwMinus : ∀ (n : ℕ) (i : Fin n) (b : B),
    coefficientMap (B := B) n b * jwMinus n i =
      jwMinus n i * coefficientMap (B := B) n b := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i b
      cases i using Fin.lastCases with
      | last =>
          rw [jwMinus_last, coefficientMap, RingHom.comp_apply]
          exact diagonalLift_comm_rotation _
      | cast i =>
          rw [jwMinus_castSucc, coefficientMap, RingHom.comp_apply]
          exact diagonalLift_comm_kleinTwist_of _ _ (ih i b)

/-- Recursive creation operators over the nested matrix stages. Old sites are
transported by the Klein grading string, and the new site is the matrix unit. -/
def jwCreate : (n : ℕ) → Fin n → OperatorStage B n
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.lastCases create (fun i => kleinTwist (jwCreate n i)) i

/-- Recursive annihilation operators, ordered as the adjoint Witt matrix unit
at each new site. -/
def jwAnnihilate : (n : ℕ) → Fin n → OperatorStage B n
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.lastCases annihilate (fun i => kleinTwist (jwAnnihilate n i)) i

@[simp] theorem jwCreate_castSucc (n : ℕ) (i : Fin n) :
    jwCreate (B := B) (n + 1) i.castSucc = kleinTwist (jwCreate n i) := by
  simp [jwCreate]

@[simp] theorem jwCreate_last (n : ℕ) :
    jwCreate (B := B) (n + 1) (Fin.last n) = create := by
  simp [jwCreate]

@[simp] theorem jwAnnihilate_castSucc (n : ℕ) (i : Fin n) :
    jwAnnihilate (B := B) (n + 1) i.castSucc = kleinTwist (jwAnnihilate n i) := by
  simp [jwAnnihilate]

@[simp] theorem jwAnnihilate_last (n : ℕ) :
    jwAnnihilate (B := B) (n + 1) (Fin.last n) = annihilate := by
  simp [jwAnnihilate]

/-- Embedded coefficients commute with all creation operators, including the
new outer-site matrix units. -/
theorem coefficientMap_comm_jwCreate : ∀ (n : ℕ) (i : Fin n) (b : B),
    coefficientMap (B := B) n b * jwCreate n i =
      jwCreate n i * coefficientMap (B := B) n b := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i b
      cases i using Fin.lastCases with
      | last =>
          rw [jwCreate_last, coefficientMap, RingHom.comp_apply]
          exact diagonalLift_comm_create _
      | cast i =>
          rw [jwCreate_castSucc, coefficientMap, RingHom.comp_apply]
          exact diagonalLift_comm_kleinTwist_of _ _ (ih i b)

/-- Embedded coefficients commute with all annihilation operators, including
the new outer-site matrix units. -/
theorem coefficientMap_comm_jwAnnihilate : ∀ (n : ℕ) (i : Fin n) (b : B),
    coefficientMap (B := B) n b * jwAnnihilate n i =
      jwAnnihilate n i * coefficientMap (B := B) n b := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i b
      cases i using Fin.lastCases with
      | last =>
          rw [jwAnnihilate_last, coefficientMap, RingHom.comp_apply]
          exact diagonalLift_comm_annihilate _
      | cast i =>
          rw [jwAnnihilate_castSucc, coefficientMap, RingHom.comp_apply]
          exact diagonalLift_comm_kleinTwist_of _ _ (ih i b)

/-- Every recursively nested creation operator is square-zero. -/
theorem jwCreate_sq : ∀ (n : ℕ) (i : Fin n),
    jwCreate (B := B) n i * jwCreate n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | last => simpa using (witt_ladder_car (A := OperatorStage B n)).1
      | cast i =>
          rw [jwCreate_castSucc]
          exact kleinTwist_sq_zero (ih i)

/-- Every recursively nested annihilation operator is square-zero. -/
theorem jwAnnihilate_sq : ∀ (n : ℕ) (i : Fin n),
    jwAnnihilate (B := B) n i * jwAnnihilate n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | last => simpa using (witt_ladder_car (A := OperatorStage B n)).2.1
      | cast i =>
          rw [jwAnnihilate_castSucc]
          exact kleinTwist_sq_zero (ih i)

/-- The same-site CAR relation holds at every recursive matrix stage. -/
theorem jwCreate_Annihilate_same_site : ∀ (n : ℕ) (i : Fin n),
    jwCreate (B := B) n i * jwAnnihilate n i +
      jwAnnihilate n i * jwCreate n i = 1 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | last => simpa using (witt_ladder_car (A := OperatorStage B n)).2.2.1
      | cast i =>
          rw [jwCreate_castSucc, jwAnnihilate_castSucc]
          calc
            kleinTwist (jwCreate n i) * kleinTwist (jwAnnihilate n i) +
                kleinTwist (jwAnnihilate n i) * kleinTwist (jwCreate n i)
                = diagonalLift (jwCreate n i * jwAnnihilate n i +
                    jwAnnihilate n i * jwCreate n i) :=
                      kleinTwist_anticomm_eq _ _
            _ = 1 := by rw [ih i, diagonalLift_one]

/-- Creation operators at distinct sites anticommute throughout the tower. -/
theorem jwCreate_cross_anticommute : ∀ (n : ℕ) (i j : Fin n), i ≠ j →
    jwCreate (B := B) n i * jwCreate n j + jwCreate n j * jwCreate n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases with
          | last => exact (hij rfl).elim
          | cast j =>
              rw [jwCreate_last, jwCreate_castSucc]
              simpa [add_comm] using
                kleinTwist_anticomm_create (A := OperatorStage B n) (jwCreate n j)
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              rw [jwCreate_castSucc, jwCreate_last]
              exact kleinTwist_anticomm_create (A := OperatorStage B n) (jwCreate n i)
          | cast j =>
              have hij' : i ≠ j := by
                intro h
                exact hij (congrArg Fin.castSucc h)
              rw [jwCreate_castSucc, jwCreate_castSucc]
              exact kleinTwist_anticomm_of (ih i j hij')

/-- Annihilation operators at distinct sites anticommute throughout the tower. -/
theorem jwAnnihilate_cross_anticommute : ∀ (n : ℕ) (i j : Fin n), i ≠ j →
    jwAnnihilate (B := B) n i * jwAnnihilate n j +
      jwAnnihilate n j * jwAnnihilate n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases with
          | last => exact (hij rfl).elim
          | cast j =>
              rw [jwAnnihilate_last, jwAnnihilate_castSucc]
              simpa [add_comm] using
                kleinTwist_anticomm_annihilate (A := OperatorStage B n) (jwAnnihilate n j)
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              rw [jwAnnihilate_castSucc, jwAnnihilate_last]
              exact kleinTwist_anticomm_annihilate (A := OperatorStage B n) (jwAnnihilate n i)
          | cast j =>
              have hij' : i ≠ j := by
                intro h
                exact hij (congrArg Fin.castSucc h)
              rw [jwAnnihilate_castSucc, jwAnnihilate_castSucc]
              exact kleinTwist_anticomm_of (ih i j hij')

/-- Creation at one site anticommutes with annihilation at every distinct site. -/
theorem jwCreateAnnihilate_cross_anticommute : ∀ (n : ℕ) (i j : Fin n), i ≠ j →
    jwCreate (B := B) n i * jwAnnihilate n j +
      jwAnnihilate n j * jwCreate n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases with
          | last => exact (hij rfl).elim
          | cast j =>
              rw [jwCreate_last, jwAnnihilate_castSucc]
              simpa [add_comm] using
                kleinTwist_anticomm_create (A := OperatorStage B n) (jwAnnihilate n j)
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              rw [jwCreate_castSucc, jwAnnihilate_last]
              exact kleinTwist_anticomm_annihilate (A := OperatorStage B n) (jwCreate n i)
          | cast j =>
              have hij' : i ≠ j := by
                intro h
                exact hij (congrArg Fin.castSucc h)
              rw [jwCreate_castSucc, jwAnnihilate_castSucc]
              exact kleinTwist_anticomm_of (ih i j hij')

private theorem coefficient_weighted_anticommutator_zero
    {R : Type*} [Ring R] (c d a b : R)
    (hcd : c * d = d * c)
    (hcb : c * b = b * c) (hda : d * a = a * d)
    (hab : a * b + b * a = 0) :
    (c * a) * (d * b) + (d * b) * (c * a) = 0 := by
  have hba : b * a = -(a * b) := by
    rw [add_comm] at hab
    exact eq_neg_of_add_eq_zero_left hab
  have hfirst : (c * a) * (d * b) = (c * d) * (a * b) := by
    calc
      (c * a) * (d * b) = c * (a * d) * b := by noncomm_ring
      _ = c * (d * a) * b := by rw [← hda]
      _ = (c * d) * (a * b) := by noncomm_ring
  have hsecond : (d * b) * (c * a) = (d * c) * (b * a) := by
    calc
      (d * b) * (c * a) = d * (b * c) * a := by noncomm_ring
      _ = d * (c * b) * a := by rw [← hcb]
      _ = (d * c) * (b * a) := by noncomm_ring
  rw [hfirst, hsecond, hcd, hba]
  noncomm_ring

private theorem coefficient_weighted_anticommutator_eq
    {R : Type*} [Ring R] (c d a b : R)
    (hcb : c * b = b * c) (hda : d * a = a * d)
    (hab : a * b + b * a = 0) :
    (c * a) * (d * b) + (d * b) * (c * a) = (c * d - d * c) * (a * b) := by
  have hba : b * a = -(a * b) := by
    rw [add_comm] at hab
    exact eq_neg_of_add_eq_zero_left hab
  have hfirst : (c * a) * (d * b) = (c * d) * (a * b) := by
    calc
      (c * a) * (d * b) = c * (a * d) * b := by noncomm_ring
      _ = c * (d * a) * b := by rw [← hda]
      _ = (c * d) * (a * b) := by noncomm_ring
  have hsecond : (d * b) * (c * a) = (d * c) * (b * a) := by
    calc
      (d * b) * (c * a) = d * (b * c) * a := by noncomm_ring
      _ = d * (c * b) * a := by rw [← hcb]
      _ = (d * c) * (b * a) := by noncomm_ring
  rw [hfirst, hsecond, hba]
  noncomm_ring

private theorem sum_square_zero_of_pairwise_anticommuting
    {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    (x : ι → R) (hsq : ∀ i, x i * x i = 0)
    (hcross : ∀ i j, i ≠ j → x i * x j + x j * x i = 0) :
    (∑ i, x i) * (∑ i, x i) = 0 := by
  classical
  have hsum : ∀ s : Finset ι,
      (∑ i ∈ s, x i) * (∑ i ∈ s, x i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        have hcrossSum :
            x i * (∑ j ∈ s, x j) + (∑ j ∈ s, x j) * x i = 0 := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_eq_zero
          intro j hj
          exact hcross i j (by
            intro hij
            subst j
            exact hi hj)
        rw [Finset.sum_insert hi]
        calc
          (x i + (∑ j ∈ s, x j)) * (x i + (∑ j ∈ s, x j)) =
              x i * x i + x i * (∑ j ∈ s, x j) +
                (∑ j ∈ s, x j) * x i +
                (∑ j ∈ s, x j) * (∑ j ∈ s, x j) := by noncomm_ring
          _ = x i * (∑ j ∈ s, x j) + (∑ j ∈ s, x j) * x i := by
              rw [hsq i, ih]
              abel
          _ = 0 := hcrossSum
  simpa using hsum (Finset.univ : Finset ι)

/-- Operator-valued annihilation charge on the finite Jordan--Wigner tower.
Each coefficient is an element of the original noncommutative ring `B`,
embedded as an operator in the full matrix stage. -/
def operatorAnnihilationCharge (n : ℕ) (w : Fin n → B) : OperatorStage B n :=
  ∑ i : Fin n, coefficientMap (B := B) n (w i) * jwAnnihilate (B := B) n i

/-- For any finite family in a ring, twice the square of its sum is the
double sum of pairwise anticommutators. This formulation is valid in every
characteristic and does not divide by two. -/
private theorem sum_square_double_anticommutator
    {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι] (x : ι → R) :
    (∑ i, x i) * (∑ i, x i) + (∑ i, x i) * (∑ i, x i) =
      ∑ i, ∑ j, (x i * x j + x j * x i) := by
  classical
  have hswap : (∑ i : ι, ∑ j : ι, x i * x j) =
      ∑ i : ι, ∑ j : ι, x j * x i := by
    rw [Finset.sum_comm]
  have hprod : (∑ i : ι, x i) * (∑ i : ι, x i) =
      ∑ i : ι, ∑ j : ι, x i * x j := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  calc
    _ = (∑ i : ι, ∑ j : ι, x i * x j) +
        (∑ i : ι, ∑ j : ι, x i * x j) := by rw [hprod]
    _ = (∑ i : ι, ∑ j : ι, x i * x j) +
        (∑ i : ι, ∑ j : ι, x j * x i) := by
          exact congrArg (fun z => (∑ i : ι, ∑ j : ι, x i * x j) + z) hswap
    _ = ∑ i : ι, ∑ j : ι, (x i * x j + x j * x i) := by
          simp only [Finset.sum_add_distrib]

/-- The anticommutator of two distinct operator-weighted Jordan--Wigner
annihilation modes is exactly the coefficient commutator times their ordered
CAR bivector. This records the noncommutative correction without assuming
the coefficients commute. -/
theorem operatorAnnihilationPair_anticommutator (n : ℕ) (w : Fin n → B)
    (i j : Fin n) (hij : i ≠ j) :
    (coefficientMap (B := B) n (w i) * jwAnnihilate (B := B) n i) *
        (coefficientMap (B := B) n (w j) * jwAnnihilate (B := B) n j) +
      (coefficientMap (B := B) n (w j) * jwAnnihilate (B := B) n j) *
        (coefficientMap (B := B) n (w i) * jwAnnihilate (B := B) n i) =
      coefficientMap (B := B) n (w i * w j - w j * w i) *
        (jwAnnihilate (B := B) n i * jwAnnihilate (B := B) n j) := by
  let c := coefficientMap (B := B) n (w i)
  let d := coefficientMap (B := B) n (w j)
  let a := jwAnnihilate (B := B) n i
  let b := jwAnnihilate (B := B) n j
  have hcd : c * d - d * c = coefficientMap (B := B) n (w i * w j - w j * w i) := by
    dsimp [c, d]
    rw [← map_mul, ← map_mul, ← map_sub]
  have hcb : c * b = b * c := coefficientMap_comm_jwAnnihilate n j (w i)
  have hda : d * a = a * d := coefficientMap_comm_jwAnnihilate n i (w j)
  have hab : a * b + b * a = 0 := jwAnnihilate_cross_anticommute n i j hij
  change (c * a) * (d * b) + (d * b) * (c * a) =
    coefficientMap (B := B) n (w i * w j - w j * w i) * (a * b)
  rw [← hcd]
  exact coefficient_weighted_anticommutator_eq c d a b hcb hda hab

private theorem operatorAnnihilationMode_sq_zero (n : ℕ) (w : Fin n → B)
    (i : Fin n) :
    (coefficientMap (B := B) n (w i) * jwAnnihilate (B := B) n i) *
      (coefficientMap (B := B) n (w i) * jwAnnihilate (B := B) n i) = 0 := by
  let c := coefficientMap (B := B) n (w i)
  let a := jwAnnihilate (B := B) n i
  have hca : c * a = a * c := coefficientMap_comm_jwAnnihilate n i (w i)
  have ha : a * a = 0 := jwAnnihilate_sq n i
  change (c * a) * (c * a) = 0
  calc
    (c * a) * (c * a) = c * c * (a * a) := by
      calc
        _ = c * (a * c) * a := by noncomm_ring
        _ = c * (c * a) * a := by rw [← hca]
        _ = c * c * (a * a) := by noncomm_ring
    _ = 0 := by rw [ha]; simp

/-- Division-free finite-depth square formula for arbitrary operator
coefficients. Twice the square is the sum of coefficient commutators paired
with the ordered annihilation bivectors. In particular, no pairwise
commutativity hypothesis is hidden in the general formula. -/
theorem operatorAnnihilationCharge_double_sq (n : ℕ) (w : Fin n → B) :
    operatorAnnihilationCharge (B := B) n w *
        operatorAnnihilationCharge (B := B) n w +
      operatorAnnihilationCharge (B := B) n w *
        operatorAnnihilationCharge (B := B) n w =
      ∑ i : Fin n, ∑ j : Fin n,
        if i = j then 0 else
          coefficientMap (B := B) n (w i * w j - w j * w i) *
            (jwAnnihilate (B := B) n i * jwAnnihilate (B := B) n j) := by
  let x : Fin n → OperatorStage B n := fun i =>
    coefficientMap (B := B) n (w i) * jwAnnihilate (B := B) n i
  change (∑ i : Fin n, x i) * (∑ i : Fin n, x i) +
      (∑ i : Fin n, x i) * (∑ i : Fin n, x i) = _
  rw [sum_square_double_anticommutator]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp [operatorAnnihilationMode_sq_zero, x]
  · simp [hij, x, operatorAnnihilationPair_anticommutator n w i j hij]

/-- At every finite tower depth, an operator-valued annihilation charge is
square-zero when its coefficients commute pairwise. The proof uses the
noncommutative coefficient map and the actual matrix CAR generators. -/
theorem operatorAnnihilationCharge_sq_zero (n : ℕ) (w : Fin n → B)
    (hw : ∀ i j, w i * w j = w j * w i) :
    operatorAnnihilationCharge (B := B) n w *
      operatorAnnihilationCharge (B := B) n w = 0 := by
  apply sum_square_zero_of_pairwise_anticommuting
  · intro i
    let c := coefficientMap (B := B) n (w i)
    let a := jwAnnihilate (B := B) n i
    have hca : c * a = a * c := coefficientMap_comm_jwAnnihilate n i (w i)
    have ha : a * a = 0 := jwAnnihilate_sq n i
    change (c * a) * (c * a) = 0
    calc
      (c * a) * (c * a) = c * c * (a * a) := by
        calc
          _ = c * (a * c) * a := by noncomm_ring
          _ = c * (c * a) * a := by rw [← hca]
          _ = c * c * (a * a) := by noncomm_ring
      _ = 0 := by rw [ha]; simp
  · intro i j hij
    let c := coefficientMap (B := B) n (w i)
    let d := coefficientMap (B := B) n (w j)
    let a := jwAnnihilate (B := B) n i
    let b := jwAnnihilate (B := B) n j
    have hcd : c * d = d * c := by
      dsimp [c, d]
      rw [← map_mul, ← map_mul, hw i j]
    have hca : c * a = a * c := coefficientMap_comm_jwAnnihilate n i (w i)
    have hcb : c * b = b * c := coefficientMap_comm_jwAnnihilate n j (w i)
    have hda : d * a = a * d := coefficientMap_comm_jwAnnihilate n i (w j)
    have hdb : d * b = b * d := coefficientMap_comm_jwAnnihilate n j (w j)
    have hab : a * b + b * a = 0 := jwAnnihilate_cross_anticommute n i j hij
    change (c * a) * (d * b) + (d * b) * (c * a) = 0
    exact coefficient_weighted_anticommutator_zero c d a b hcd hcb hda hab

/-- A two-site annihilation operator with coefficients from the original
possibly noncommutative ring. The coefficients are embedded as operators at
the base of the recursively nested matrix algebra. -/
def weightedAnnihilation2 (c₀ c₁ : B) : OperatorStage B 2 :=
  coefficientMap (B := B) 2 c₀ * jwAnnihilate (B := B) 2 0 +
    coefficientMap (B := B) 2 c₁ * jwAnnihilate (B := B) 2 1

/-- Exact square of a two-site operator-weighted CAR mode. Noncommuting
operator weights leave the commutator defect `[c₀,c₁] a₀ a₁`; thus the
scalar-weight nilpotence law extends precisely when the two operator
coefficients commute (or the displayed product vanishes for another reason). -/
theorem weightedAnnihilation2_sq (c₀ c₁ : B) :
    weightedAnnihilation2 (B := B) c₀ c₁ *
        weightedAnnihilation2 (B := B) c₀ c₁ =
      coefficientMap (B := B) 2 (c₀ * c₁ - c₁ * c₀) *
        (jwAnnihilate (B := B) 2 0 * jwAnnihilate (B := B) 2 1) := by
  let u : OperatorStage B 2 := coefficientMap (B := B) 2 c₀
  let v : OperatorStage B 2 := coefficientMap (B := B) 2 c₁
  let a : OperatorStage B 2 := jwAnnihilate (B := B) 2 0
  let b : OperatorStage B 2 := jwAnnihilate (B := B) 2 1
  have hu_mul : u * v = coefficientMap (B := B) 2 (c₀ * c₁) := by
    dsimp [u, v]
    exact (map_mul (coefficientMap (B := B) 2) c₀ c₁).symm
  have hv_mul : v * u = coefficientMap (B := B) 2 (c₁ * c₀) := by
    dsimp [u, v]
    exact (map_mul (coefficientMap (B := B) 2) c₁ c₀).symm
  have hu_a : u * a = a * u := by
    exact coefficientMap_comm_jwAnnihilate 2 0 c₀
  have hu_b : u * b = b * u := by
    exact coefficientMap_comm_jwAnnihilate 2 1 c₀
  have hv_a : v * a = a * v := by
    exact coefficientMap_comm_jwAnnihilate 2 0 c₁
  have hv_b : v * b = b * v := by
    exact coefficientMap_comm_jwAnnihilate 2 1 c₁
  have ha_sq : a * a = 0 := jwAnnihilate_sq 2 0
  have hb_sq : b * b = 0 := jwAnnihilate_sq 2 1
  have hab : a * b + b * a = 0 := by
    exact jwAnnihilate_cross_anticommute 2 0 1 (by decide)
  have hba : b * a = -(a * b) := by
    rw [add_comm] at hab
    exact eq_neg_of_add_eq_zero_left hab
  have huu : (u * a) * (u * a) = 0 := by
    calc
      (u * a) * (u * a) = u * u * (a * a) := by
        calc
          _ = u * (a * u) * a := by noncomm_ring
          _ = u * (u * a) * a := by rw [← hu_a]
          _ = u * u * (a * a) := by noncomm_ring
      _ = 0 := by rw [ha_sq]; simp
  have hvv : (v * b) * (v * b) = 0 := by
    calc
      (v * b) * (v * b) = v * v * (b * b) := by
        calc
          _ = v * (b * v) * b := by noncomm_ring
          _ = v * (v * b) * b := by rw [← hv_b]
          _ = v * v * (b * b) := by noncomm_ring
      _ = 0 := by rw [hb_sq]; simp
  have huv : (u * a) * (v * b) = (u * v) * (a * b) := by
    calc
      (u * a) * (v * b) = u * (a * v) * b := by noncomm_ring
      _ = u * (v * a) * b := by rw [← hv_a]
      _ = (u * v) * (a * b) := by noncomm_ring
  have hvu : (v * b) * (u * a) = (v * u) * (b * a) := by
    calc
      (v * b) * (u * a) = v * (b * u) * a := by noncomm_ring
      _ = v * (u * b) * a := by rw [← hu_b]
      _ = (v * u) * (b * a) := by noncomm_ring
  have hcoef : u * v - v * u =
      coefficientMap (B := B) 2 (c₀ * c₁ - c₁ * c₀) := by
    rw [hu_mul, hv_mul, map_sub]
  change (u * a + v * b) * (u * a + v * b) = _
  calc
    (u * a + v * b) * (u * a + v * b) =
        (u * a) * (u * a) + (u * a) * (v * b) +
          (v * b) * (u * a) + (v * b) * (v * b) := by noncomm_ring
    _ = (u * v) * (a * b) + (v * u) * (b * a) := by
      rw [huu, hvv, huv, hvu]
      simp
    _ = (u * v - v * u) * (a * b) := by rw [hba]; noncomm_ring
    _ = coefficientMap (B := B) 2 (c₀ * c₁ - c₁ * c₀) *
          (jwAnnihilate (B := B) 2 0 * jwAnnihilate (B := B) 2 1) := by
      rw [hcoef]

/-- Matrix-unit coefficients in `M₂(ℤ)` give a genuine nonzero example of
the two-site commutator defect. This witnesses that operator-valued weights
cannot be treated as scalar weights in the nilpotence argument. -/
abbrev IntegerOperator := Matrix (Fin 2) (Fin 2) ℤ

def integerOperator01 : IntegerOperator := !![0, 1; 0, 0]
def integerOperator10 : IntegerOperator := !![0, 0; 1, 0]

theorem weightedAnnihilation2_matrix_coefficients_not_nilpotent :
    weightedAnnihilation2 (B := IntegerOperator)
        integerOperator01 integerOperator10 *
      weightedAnnihilation2 (B := IntegerOperator)
        integerOperator01 integerOperator10 ≠ 0 := by
  rw [weightedAnnihilation2_sq]
  decide

/-- The complete finite CAR matrix: the creation/annihilation anticommutator
is the Kronecker delta on site indices. -/
theorem jwCreateAnnihilate_anticommutator (n : ℕ) (i j : Fin n) :
    jwCreate (B := B) n i * jwAnnihilate n j +
      jwAnnihilate n j * jwCreate n i = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [jwCreate_Annihilate_same_site]
  · simp [h, jwCreateAnnihilate_cross_anticommute n i j h]


/-! At each site the ordered CAR products are complementary Peirce
idempotents. Their order matters: they are respectively `cᵢ aᵢ` and
`aᵢ cᵢ`, and the proof uses the same-site CAR together with square-zero. -/

theorem jwPeirce_create_annihilate_idempotent (n : ℕ) (i : Fin n) :
    (jwCreate (B := B) n i * jwAnnihilate n i) *
      (jwCreate n i * jwAnnihilate n i) =
        jwCreate n i * jwAnnihilate n i := by
  let c : OperatorStage B n := jwCreate (B := B) n i
  let a : OperatorStage B n := jwAnnihilate (B := B) n i
  have hCAR : c * a + a * c = 1 := jwCreate_Annihilate_same_site n i
  have hac : a * c = 1 - c * a := by
    calc
      a * c = (c * a + a * c) - c * a := by noncomm_ring
      _ = 1 - c * a := by rw [hCAR]
  have hcc : c * c = 0 := jwCreate_sq n i
  have haa : a * a = 0 := jwAnnihilate_sq n i
  change (c * a) * (c * a) = c * a
  calc
    (c * a) * (c * a) = c * (a * c) * a := by noncomm_ring
    _ = c * (1 - c * a) * a := by rw [hac]
    _ = c * a - (c * c) * (a * a) := by noncomm_ring
    _ = c * a := by rw [hcc, haa]; simp

theorem jwPeirce_annihilate_create_idempotent (n : ℕ) (i : Fin n) :
    (jwAnnihilate (B := B) n i * jwCreate n i) *
      (jwAnnihilate n i * jwCreate n i) =
        jwAnnihilate n i * jwCreate n i := by
  let c : OperatorStage B n := jwCreate (B := B) n i
  let a : OperatorStage B n := jwAnnihilate (B := B) n i
  have hCAR : c * a + a * c = 1 := jwCreate_Annihilate_same_site n i
  have hca : c * a = 1 - a * c := by
    calc
      c * a = (c * a + a * c) - a * c := by noncomm_ring
      _ = 1 - a * c := by rw [hCAR]
  have hcc : c * c = 0 := jwCreate_sq n i
  have haa : a * a = 0 := jwAnnihilate_sq n i
  change (a * c) * (a * c) = a * c
  calc
    (a * c) * (a * c) = a * (c * a) * c := by noncomm_ring
    _ = a * (1 - a * c) * c := by rw [hca]
    _ = a * c - (a * a) * (c * c) := by noncomm_ring
    _ = a * c := by rw [haa, hcc]; simp

theorem jwPeirce_create_annihilate_mul_opposite (n : ℕ) (i : Fin n) :
    (jwCreate (B := B) n i * jwAnnihilate n i) *
      (jwAnnihilate n i * jwCreate n i) = 0 := by
  let c : OperatorStage B n := jwCreate (B := B) n i
  let a : OperatorStage B n := jwAnnihilate (B := B) n i
  have haa : a * a = 0 := jwAnnihilate_sq n i
  change (c * a) * (a * c) = 0
  calc
    (c * a) * (a * c) = (c * (a * a)) * c := by noncomm_ring
    _ = 0 := by rw [haa]; simp

theorem jwPeirce_annihilate_create_mul_opposite (n : ℕ) (i : Fin n) :
    (jwAnnihilate (B := B) n i * jwCreate n i) *
      (jwCreate n i * jwAnnihilate n i) = 0 := by
  let c : OperatorStage B n := jwCreate (B := B) n i
  let a : OperatorStage B n := jwAnnihilate (B := B) n i
  have hcc : c * c = 0 := jwCreate_sq n i
  change (a * c) * (c * a) = 0
  calc
    (a * c) * (c * a) = (a * (c * c)) * a := by noncomm_ring
    _ = 0 := by rw [hcc]; simp

/-- Ordered creation/annihilation products give the two complementary site
Peirce idempotents at every finite stage. -/
theorem jwSitePeirce_relations (n : ℕ) (i : Fin n) :
    (jwCreate (B := B) n i * jwAnnihilate n i) *
        (jwCreate n i * jwAnnihilate n i) = jwCreate n i * jwAnnihilate n i ∧
    (jwAnnihilate (B := B) n i * jwCreate n i) *
        (jwAnnihilate n i * jwCreate n i) = jwAnnihilate n i * jwCreate n i ∧
    (jwCreate (B := B) n i * jwAnnihilate n i) *
        (jwAnnihilate n i * jwCreate n i) = 0 ∧
    (jwAnnihilate (B := B) n i * jwCreate n i) *
        (jwCreate n i * jwAnnihilate n i) = 0 ∧
    jwCreate (B := B) n i * jwAnnihilate n i +
        jwAnnihilate n i * jwCreate n i = 1 := by
  exact ⟨jwPeirce_create_annihilate_idempotent n i,
    jwPeirce_annihilate_create_idempotent n i,
    jwPeirce_create_annihilate_mul_opposite n i,
    jwPeirce_annihilate_create_mul_opposite n i,
    jwCreate_Annihilate_same_site n i⟩

theorem jwPlus_sq : ∀ (n : ℕ) (i : Fin n),
    jwPlus (B := B) n i * jwPlus n i = 1 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | last =>
          simpa [jwPlus] using (shift_sq (A := OperatorStage B n))
      | cast i =>
          have h : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n := by
            simpa using i.isLt
          simp only [jwPlus, dif_pos h]
          change ((kleinTwist (jwPlus n i) : Op₂ (OperatorStage B n)) *
            kleinTwist (jwPlus n i)) = (1 : Op₂ (OperatorStage B n))
          calc
            kleinTwist (jwPlus n i) * kleinTwist (jwPlus n i)
                = diagonalLift (jwPlus n i * jwPlus n i) :=
                    kleinTwist_mul (jwPlus n i) (jwPlus n i)
            _ = 1 := by rw [ih i, diagonalLift_one]

theorem jwMinus_sq : ∀ (n : ℕ) (i : Fin n),
    jwMinus (B := B) n i * jwMinus n i = -1 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | last =>
          simpa [jwMinus] using (rotation_sq (A := OperatorStage B n))
      | cast i =>
          have h : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n := by
            simpa using i.isLt
          simp only [jwMinus, dif_pos h]
          change ((kleinTwist (jwMinus n i) : Op₂ (OperatorStage B n)) *
            kleinTwist (jwMinus n i)) = (-1 : Op₂ (OperatorStage B n))
          calc
            kleinTwist (jwMinus n i) * kleinTwist (jwMinus n i)
                = diagonalLift (jwMinus n i * jwMinus n i) :=
                    kleinTwist_mul (jwMinus n i) (jwMinus n i)
            _ = -1 := by rw [ih i, diagonalLift_neg_one]

/-- Distinct positive Clifford generators anticommute at every finite stage. -/
theorem jwPlus_cross_anticommute : ∀ (n : ℕ) (i j : Fin n), i ≠ j →
    jwPlus (B := B) n i * jwPlus n j + jwPlus n j * jwPlus n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases with
          | last => exact (hij rfl).elim
          | cast j =>
              rw [jwPlus_last, jwPlus_castSucc]
              simpa [add_comm] using
                (kleinTwist_anticomm_shift (A := OperatorStage B n) (jwPlus n j))
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              rw [jwPlus_castSucc, jwPlus_last]
              exact kleinTwist_anticomm_shift (A := OperatorStage B n) (jwPlus n i)
          | cast j =>
              have hij' : i ≠ j := by
                intro h
                exact hij (congrArg Fin.castSucc h)
              rw [jwPlus_castSucc, jwPlus_castSucc]
              exact kleinTwist_anticomm_of (ih i j hij')

/-- Distinct negative Clifford generators anticommute at every finite stage. -/
theorem jwMinus_cross_anticommute : ∀ (n : ℕ) (i j : Fin n), i ≠ j →
    jwMinus (B := B) n i * jwMinus n j + jwMinus n j * jwMinus n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases with
          | last => exact (hij rfl).elim
          | cast j =>
              rw [jwMinus_last, jwMinus_castSucc]
              simpa [add_comm] using
                (kleinTwist_anticomm_rotation (A := OperatorStage B n) (jwMinus n j))
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              rw [jwMinus_castSucc, jwMinus_last]
              exact kleinTwist_anticomm_rotation (A := OperatorStage B n) (jwMinus n i)
          | cast j =>
              have hij' : i ≠ j := by
                intro h
                exact hij (congrArg Fin.castSucc h)
              rw [jwMinus_castSucc, jwMinus_castSucc]
              exact kleinTwist_anticomm_of (ih i j hij')

/-- Every positive generator anticommutes with every negative generator,
including at the same site, in the recursively nested matrix representation. -/
theorem jwPlus_jwMinus_anticommute : ∀ (n : ℕ) (i j : Fin n),
    jwPlus (B := B) n i * jwMinus n j + jwMinus n j * jwPlus n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i j
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases with
          | last => simpa using shift_anticomm_rotation (A := OperatorStage B n)
          | cast j =>
              rw [jwPlus_last, jwMinus_castSucc]
              simpa [add_comm] using
                (kleinTwist_anticomm_shift (A := OperatorStage B n) (jwMinus n j))
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              rw [jwPlus_castSucc, jwMinus_last]
              exact kleinTwist_anticomm_rotation (A := OperatorStage B n) (jwPlus n i)
          | cast j =>
              rw [jwPlus_castSucc, jwMinus_castSucc]
              exact kleinTwist_anticomm_of (ih i j)

/-- The Jordan--Wigner matrix generators satisfy the `Cl(n,n)` quadratic
relations at every finite stage: positive generators have anticommutator
`2 δᵢⱼ`, negative generators have anticommutator `-2 δᵢⱼ`, and the two
families anticommute with each other. This is a representation-level relation
theorem in `OperatorStage B n`, not a universal-algebra isomorphism claim. -/
theorem jwPlus_clifford_anticommutator (n : ℕ) (i j : Fin n) :
    jwPlus (B := B) n i * jwPlus n j + jwPlus n j * jwPlus n i =
      if i = j then (1 : OperatorStage B n) + 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [jwPlus_sq]
  · simp [h, jwPlus_cross_anticommute n i j h]

theorem jwMinus_clifford_anticommutator (n : ℕ) (i j : Fin n) :
    jwMinus (B := B) n i * jwMinus n j + jwMinus n j * jwMinus n i =
      if i = j then (-1 : OperatorStage B n) + (-1) else 0 := by
  by_cases h : i = j
  · subst j
    simp [jwMinus_sq]
  · simp [h, jwMinus_cross_anticommute n i j h]

theorem jwClifford_polar_relations (n : ℕ) (i j : Fin n) :
    (jwPlus (B := B) n i * jwPlus n j + jwPlus n j * jwPlus n i =
      if i = j then (1 : OperatorStage B n) + 1 else 0) ∧
    (jwMinus (B := B) n i * jwMinus n j + jwMinus n j * jwMinus n i =
      if i = j then (-1 : OperatorStage B n) + (-1) else 0) ∧
    jwPlus (B := B) n i * jwMinus n j + jwMinus n j * jwPlus n i = 0 := by
  exact ⟨jwPlus_clifford_anticommutator n i j,
    jwMinus_clifford_anticommutator n i j,
    jwPlus_jwMinus_anticommute n i j⟩

/-- The all-site signed Clifford anticommutator laws in the explicit standard
full matrix carrier of dimension `2^n`. -/
theorem operatorStageFinMatrixEquiv_jwClifford_relations (n : ℕ)
    (i j : Fin n) :
    ((operatorStageFinMatrixEquiv (B := B) n) (jwPlus n i) *
        (operatorStageFinMatrixEquiv (B := B) n) (jwPlus n j) +
      (operatorStageFinMatrixEquiv (B := B) n) (jwPlus n j) *
        (operatorStageFinMatrixEquiv (B := B) n) (jwPlus n i) =
      if i = j then (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B) + 1 else 0) ∧
    ((operatorStageFinMatrixEquiv (B := B) n) (jwMinus n i) *
        (operatorStageFinMatrixEquiv (B := B) n) (jwMinus n j) +
      (operatorStageFinMatrixEquiv (B := B) n) (jwMinus n j) *
        (operatorStageFinMatrixEquiv (B := B) n) (jwMinus n i) =
      if i = j then (-1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B) + (-1) else 0) ∧
    (operatorStageFinMatrixEquiv (B := B) n) (jwPlus n i) *
        (operatorStageFinMatrixEquiv (B := B) n) (jwMinus n j) +
      (operatorStageFinMatrixEquiv (B := B) n) (jwMinus n j) *
        (operatorStageFinMatrixEquiv (B := B) n) (jwPlus n i) = 0 := by
  let E := operatorStageFinMatrixEquiv (B := B) n
  have hp := congrArg E
    (jwPlus_clifford_anticommutator (B := B) n i j)
  have hm := congrArg E
    (jwMinus_clifford_anticommutator (B := B) n i j)
  have hpm := congrArg E
    (jwPlus_jwMinus_anticommute (B := B) n i j)
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : i = j
    · subst j
      simpa [E] using hp
    · simpa [E, h] using hp
  · by_cases h : i = j
    · subst j
      simpa [E] using hm
    · simpa [E, h] using hm
  · simpa [E] using hpm

/-- Creation and annihilation operators satisfy the sitewise CAR directly in
the standard `2^n × 2^n` matrix representation, with the Kronecker delta on
sites. The coefficient ring remains arbitrary and is not assumed
commutative. -/
theorem operatorStageFinMatrixEquiv_jwCAR (n : ℕ) (i j : Fin n) :
    let E := operatorStageFinMatrixEquiv (B := B) n
    E (jwCreate n i) * E (jwAnnihilate n j) +
      E (jwAnnihilate n j) * E (jwCreate n i) =
        if i = j then (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B) else 0 := by
  let E := operatorStageFinMatrixEquiv (B := B) n
  have h := congrArg E (jwCreateAnnihilate_anticommutator (B := B) n i j)
  by_cases hij : i = j
  · subst j
    simpa [E] using h
  · simpa [E, hij] using h

/-- The ordered site occupation operators remain complementary idempotents
after passing to the explicit full-matrix carrier. This records the order of
creation and annihilation rather than replacing them by scalar projections. -/
theorem operatorStageFinMatrixEquiv_jwSitePeirce (n : ℕ) (i : Fin n) :
    let E := operatorStageFinMatrixEquiv (B := B) n
    (E (jwCreate n i) * E (jwAnnihilate n i)) *
        (E (jwCreate n i) * E (jwAnnihilate n i)) =
          E (jwCreate n i) * E (jwAnnihilate n i) ∧
    (E (jwAnnihilate n i) * E (jwCreate n i)) *
        (E (jwAnnihilate n i) * E (jwCreate n i)) =
          E (jwAnnihilate n i) * E (jwCreate n i) ∧
    (E (jwCreate n i) * E (jwAnnihilate n i)) *
        (E (jwAnnihilate n i) * E (jwCreate n i)) = 0 ∧
    (E (jwAnnihilate n i) * E (jwCreate n i)) *
        (E (jwCreate n i) * E (jwAnnihilate n i)) = 0 := by
  let E := operatorStageFinMatrixEquiv (B := B) n
  have h := jwSitePeirce_relations (B := B) n i
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [E] using congrArg E h.1
  · simpa [E] using congrArg E h.2.1
  · simpa [E] using congrArg E h.2.2.1
  · simpa [E] using congrArg E h.2.2.2.1

end RecursiveTower

end InfoGeometry.Clifford.BrauerWeylMatrixStep
