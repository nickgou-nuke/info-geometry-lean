import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open Matrix
open scoped BigOperators

namespace InfoGeometry.Amplituhedron

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### 1. 2x2 Plücker Minors and 4x4 Determinants -/

def minor2 (C : Matrix (Fin 2) (Fin n) R) (a b : Fin n) : R :=
  C 0 a * C 1 b - C 1 a * C 0 b

theorem minor2_skew (C : Matrix (Fin 2) (Fin n) R) (a b : Fin n) :
    minor2 C b a = - minor2 C a b := by
  dsimp [minor2]
  ring

theorem minor2_self (C : Matrix (Fin 2) (Fin n) R) (a : Fin n) :
    minor2 C a a = 0 := by
  dsimp [minor2]
  ring

/-- The three-term Plücker relation for the 2x2 minors of a two-row matrix. -/
theorem plucker_relation_general (C : Matrix (Fin 2) (Fin n) R) (a b c d : Fin n) :
    minor2 C a c * minor2 C b d =
      minor2 C a b * minor2 C c d + minor2 C a d * minor2 C b c := by
  dsimp [minor2]
  ring

def det4 (M : Matrix (Fin 4) (Fin 4) R) : R :=
  M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
           M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) +
           M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
  M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
           M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
           M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
  M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
           M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
           M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
  M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
           M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) +
           M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))

/-- The explicit four-by-four Laplace polynomial agrees with Mathlib's determinant. -/
theorem det4_eq_matrix_det (M : Matrix (Fin 4) (Fin 4) R) : det4 M = M.det := by
  rw [Matrix.det_succ_row_zero]
  simp [det4, Matrix.det_fin_three, Fin.sum_univ_four, Fin.succAbove]
  ring_nf

/-- Strict total positivity of a 2x4 matrix, expressed by its six Plücker minors. -/
def IsTotallyPositive24 (C : Matrix (Fin 2) (Fin 4) ℝ) : Prop :=
  0 < minor2 C 0 1 ∧
  0 < minor2 C 0 2 ∧
  0 < minor2 C 0 3 ∧
  0 < minor2 C 1 2 ∧
  0 < minor2 C 1 3 ∧
  0 < minor2 C 2 3

/-! ### 2. The General Kinematic Twistor Projection Y = C * Z -/

def twistorProj (C : Matrix (Fin 2) (Fin n) R) (Z : Matrix (Fin n) (Fin 4) R) :
    Matrix (Fin 2) (Fin 4) R :=
  C * Z

lemma twistorProj_fin4_apply (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R)
    (r : Fin 2) (c : Fin 4) :
    twistorProj C Z r c =
      C r 0 * Z 0 c + C r 1 * Z 1 c + C r 2 * Z 2 c + C r 3 * Z 3 c := by
  dsimp [twistorProj, Matrix.mul_apply]
  rw [Fin.sum_univ_four]

def twistorMatrix (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R) (a b : Fin n) :
    Matrix (Fin 4) (Fin 4) R :=
  fun r c =>
    if r = 0 then Y 0 c
    else if r = 1 then Y 1 c
    else if r = 2 then Z a c
    else Z b c

omit [CommRing R] in
@[simp] lemma twistorMatrix_row0 (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R)
    (a b : Fin n) (c : Fin 4) : twistorMatrix Y Z a b 0 c = Y 0 c := rfl

omit [CommRing R] in
@[simp] lemma twistorMatrix_row1 (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R)
    (a b : Fin n) (c : Fin 4) : twistorMatrix Y Z a b 1 c = Y 1 c := rfl

omit [CommRing R] in
@[simp] lemma twistorMatrix_row2 (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R)
    (a b : Fin n) (c : Fin 4) : twistorMatrix Y Z a b 2 c = Z a c := rfl

omit [CommRing R] in
@[simp] lemma twistorMatrix_row3 (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R)
    (a b : Fin n) (c : Fin 4) : twistorMatrix Y Z a b 3 c = Z b c := rfl

def twistorBracket (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin n) (Fin 4) R) (a b : Fin n) : R :=
  det4 (twistorMatrix Y Z a b)

def externalBracket (Z : Matrix (Fin n) (Fin 4) R) (i j a b : Fin n) : R :=
  det4 (fun r c =>
    if r = 0 then Z i c
    else if r = 1 then Z j c
    else if r = 2 then Z a c
    else Z b c)

/-! ### 3. Cyclic Bracket Denominator -/

/-- Shift an index cyclicly modulo n for the physical boundaries. -/
def cyclicNext [NeZero n] (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, NeZero.pos n⟩

/-- The cyclic product of adjacent four-brackets used as a denominator in
candidate rational expressions. -/
noncomputable def cyclicTwistorDenominator [NeZero n]
    (Y : Matrix (Fin 2) (Fin 4) ℝ) (Z : Matrix (Fin n) (Fin 4) ℝ) : ℝ :=
  ∏ i : Fin n, twistorBracket Y Z i (cyclicNext i)

/-- Positivity of every cyclic bracket makes the cyclic denominator positive.
This is denominator regularity only; no canonical differential form is defined here. -/
theorem cyclicTwistorDenominator_pos [NeZero n]
    (Y : Matrix (Fin 2) (Fin 4) ℝ) (Z : Matrix (Fin n) (Fin 4) ℝ)
    (h : ∀ i : Fin n, 0 < twistorBracket Y Z i (cyclicNext i)) :
    0 < cyclicTwistorDenominator Y Z := by
  exact Finset.prod_pos fun i _ => h i

end InfoGeometry.Amplituhedron
