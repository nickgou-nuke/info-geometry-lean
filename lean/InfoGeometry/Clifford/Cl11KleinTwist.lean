/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SplitAtomDoubling.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel

/-!
# Klein lifts with noncommutative coefficients

The repeated and twisted embeddings are owned by `SplitAtomDoubling.Basic`.
The owner convention is `negative = !![0, 1; -1, 0]`, so the chirality is
`-(positive * negative)`. A twist of every element is not in general multiplicative;
`gradedEmbed` supplies the actual ring homomorphism `a ↦ diag(a, σ(a))`.

Native matrix units give the algebraic CAR and exact reconstruction without
division by two. The signed four-term identity reconstructs `M + M`, with
no claim to be a Mellin transform or a graded tensor algebra equivalence.
-/

namespace InfoGeometry.Clifford.SplitAtomDoubling

variable {A : Type*} [Ring A]

/-- The chirality implementing the outer block grading. -/
def parity : Block2 A := twisted 1

@[simp] theorem repeated_zero : repeated (0 : A) = 0 := repeatedHom.map_zero

@[simp] theorem repeated_one : repeated (1 : A) = 1 := repeatedHom.map_one

@[simp] theorem repeated_neg (a : A) : repeated (-a) = -repeated a :=
  repeatedHom.map_neg a

theorem repeated_injective : Function.Injective (repeated (A := A)) := by
  intro a b h
  exact congrArg (fun M : Block2 A => M 0 0) h

/-- The twist is an additive homomorphism, with no multiplication law assumed. -/
def twistedAddHom : A →+ Block2 A where
  toFun := twisted
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twisted]
  map_add' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twisted, add_comm]

@[simp] theorem twisted_zero : twisted (0 : A) = 0 := twistedAddHom.map_zero

theorem repeated_mul_twisted (a b : A) :
    repeated a * twisted b = twisted (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [repeated, twisted, Matrix.mul_apply, Fin.sum_univ_two]

theorem twisted_mul_repeated (a b : A) :
    twisted a * repeated b = twisted (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [repeated, twisted, Matrix.mul_apply, Fin.sum_univ_two]

/-- Commutator order is preserved; no coefficients are commuted. -/
theorem twisted_commutator (a b : A) :
    twisted a * twisted b - twisted b * twisted a = repeated (a * b - b * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twisted, repeated]

/-- The lift preserves a genuine failure of commutation in either direction. -/
theorem twisted_mul_ne_swap_iff (a b : A) :
    twisted a * twisted b ≠ twisted b * twisted a ↔ a * b ≠ b * a := by
  rw [twisted_mul, twisted_mul]
  exact repeated_injective.ne_iff

@[simp] theorem parity_square : (parity : Block2 A) * parity = 1 := by
  simp [parity, twisted_mul]

theorem positive_mul_negative :
    (positive : Block2 A) * negative = -parity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, negative, parity, twisted, Matrix.mul_apply, Fin.sum_univ_two]

theorem parity_positive_anticommutator :
    (parity : Block2 A) * positive + positive * parity = 0 :=
  twisted_positive_anticommutator 1

theorem parity_negative_anticommutator :
    (parity : Block2 A) * negative + negative * parity = 0 :=
  twisted_negative_anticommutator 1

theorem twisted_eq_repeated_mul_parity (a : A) :
    twisted a = repeated a * parity := by
  simp [parity, repeated_mul_twisted]

/-- The twisted coefficient is even for the *outer* block grading. -/
theorem parity_commutes_twisted (a : A) :
    parity * twisted a = twisted a * parity := by
  simp [parity, twisted_mul]

/-- The repeated coefficient commutes with every scalar matrix unit. -/
theorem repeated_commutes_single (a : A) (i j : Fin 2) :
    repeated a * Matrix.single i j 1 = Matrix.single i j 1 * repeated a := by
  ext k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [repeated, Matrix.single_apply, Matrix.mul_apply]

/-- A multiplicative parity-sensitive embedding, valid for every ring endomorphism.
For an involutive grading, even coefficients use `repeated` and odd ones use `twisted`. -/
def gradedEmbed (σ : A →+* A) : A →+* Block2 A where
  toFun a := !![a, 0; 0, σ a]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem gradedEmbed_injective (σ : A →+* A) : Function.Injective (gradedEmbed σ) := by
  intro a b h
  exact congrArg (fun M : Block2 A => M 0 0) h

theorem gradedEmbed_of_even (σ : A →+* A) {a : A} (h : σ a = a) :
    gradedEmbed σ a = repeated a := by
  simp [gradedEmbed, repeated, h]

theorem gradedEmbed_of_odd (σ : A →+* A) {a : A} (h : σ a = -a) :
    gradedEmbed σ a = twisted a := by
  simp [gradedEmbed, twisted, h]

/-- Conjugation by the outer swap implements the given involutive grading
on its embedded copy of the full coefficient ring. -/
theorem positive_gradedEmbed_conjugation (σ : A →+* A)
    (hσ : Function.Involutive σ) (a : A) :
    positive * gradedEmbed σ a * positive = gradedEmbed σ (σ a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, gradedEmbed, Matrix.mul_apply, Fin.sum_univ_two, hσ a]

/-- The obstruction to viewing the all-element twist as a unital map. -/
theorem twisted_one_eq_one_iff :
    twisted (1 : A) = 1 ↔ (2 : A) = 0 := by
  constructor
  · intro h
    have h11 : -(1 : A) = 1 := congrArg (fun M : Block2 A => M 1 1) h
    have hsum : (1 : A) + 1 = 0 := by calc
      (1 : A) + 1 = 1 + -1 := congrArg ((1 : A) + ·) h11.symm
      _ = 0 := add_neg_cancel 1
    simpa only [one_add_one_eq_two] using hsum
  · intro h
    have hsum : (1 : A) + 1 = 0 := by simpa only [one_add_one_eq_two] using h
    have hneg : -(1 : A) = 1 := (eq_neg_of_add_eq_zero_left hsum).symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twisted, hneg]

section MatrixUnits

open Matrix

/-- The upper transition unit is the corresponding Peirce corner of the swap. -/
theorem raising_eq_peirce :
    (single 0 1 (1 : A) : Block2 A) =
      single 0 0 1 * positive * single 1 1 1 := by
  simp [positive]

/-- The lower transition unit is the opposite Peirce corner. -/
theorem lowering_eq_peirce :
    (single 1 0 (1 : A) : Block2 A) =
      single 1 1 1 * positive * single 0 0 1 := by
  simp [positive]

theorem raising_add_lowering :
    (single 0 1 (1 : A) : Block2 A) + single 1 0 1 = positive := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [positive]

theorem raising_sub_lowering :
    (single 0 1 (1 : A) : Block2 A) - single 1 0 1 = negative := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negative]

theorem raising_sq_zero :
    single (0 : Fin 2) (1 : Fin 2) (1 : A) * single 0 1 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [single_apply, mul_apply]

theorem lowering_sq_zero :
    single (1 : Fin 2) (0 : Fin 2) (1 : A) * single 1 0 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [single_apply, mul_apply]

theorem raising_lowering_car :
    single (0 : Fin 2) (1 : Fin 2) (1 : A) * single 1 0 1 +
      single 1 0 1 * single 0 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp

theorem raising_lowering_commutator :
    single (0 : Fin 2) (1 : Fin 2) (1 : A) * single 1 0 1 -
      single 1 0 1 * single 0 1 1 = parity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parity, twisted]

theorem twisted_raising_anticommutator (a : A) :
    twisted a * single 0 1 1 + single 0 1 1 * twisted a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    simp [twisted]

theorem twisted_lowering_anticommutator (a : A) :
    twisted a * single 1 0 1 + single 1 0 1 * twisted a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    simp [twisted]

/-- Exact reconstruction, including in characteristic two and with noncommuting entries. -/
theorem matrix_unit_reconstruction (M : Block2 A) :
    repeated (M 0 0) * single 0 0 1 + repeated (M 0 1) * single 0 1 1 +
      repeated (M 1 0) * single 1 0 1 + repeated (M 1 1) * single 1 1 1 = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    simp [repeated]

/-- The upper-left Peirce corner and its swapped negative give the Klein lift. -/
theorem twisted_eq_corner_difference (M : Block2 A) :
    twisted (M 0 0) =
      single 0 0 1 * M * single 0 0 1 -
        positive * single 0 0 1 * M * single 0 0 1 * positive := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    simp [twisted, positive]

end MatrixUnits

/-- The source's four-term formula with the owner's opposite `negative` sign.
It reconstructs exactly twice the matrix, with no implicit division by two. -/
theorem doubled_klein_reconstruction (M : Block2 A) :
    twisted ((M - positive * M * positive : Block2 A) 0 0) +
      twisted ((M + positive * M * positive : Block2 A) 0 0) * parity -
      twisted ((positive * M - M * positive : Block2 A) 0 0) * positive +
      twisted ((M * positive + positive * M : Block2 A) 0 0) * negative = M + M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    simp [twisted, parity, positive, negative] <;> abel

end InfoGeometry.Clifford.SplitAtomDoubling
