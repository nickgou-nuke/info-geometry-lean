/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Clifford.SignedPermutation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Transpose parity of indexed real Pauli tensor words

The alphabet is the existing real matrix family `[1, Eplus, J1, Eminus]`.
Only `Eminus` is skew under transpose. Evaluation uses the native recursive
`TowerMatrix.Mat`: `evaluate (Fin.cons a w) = evaluate w ⊗ₖ realSeed a`.
Thus word position zero labels the rightmost tensor factor; the retained
`Fin 1` factor at level zero acts as the scalar unit.

`wordCount n b` is the cardinality of actual words with Boolean parity `b`.
The recurrence is proved from the head/tail equivalence, not used to define
the count. Every evaluated word is orthogonal and nonzero. No injectivity of
the complete evaluation family, basis theorem, dimension formula, or count
of all nondegenerate bilinear forms is asserted.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11TensorTransposeCensus

open InfoGeometry.Clifford.Cl11Matrix InfoGeometry.Clifford.TowerMatrix
open scoped Matrix Kronecker

abbrev Word (n : ℕ) := Fin n → Fin 4

/-- The existing three symmetric seeds and one skew seed. -/
def realSeed : Fin 4 → Mat2 := ![1, Eplus, J1, Eminus]

/-- Head insertion appends the corresponding seed on the right. -/
def evaluate : {n : ℕ} → Word n → Mat n
  | 0, _ => 1
  | n + 1, w => evaluate (Fin.tail w) ⊗ₖ realSeed (w 0)

/-- Each occurrence of the unique skew letter flips transpose parity. -/
def oddEminus : {n : ℕ} → Word n → Bool
  | 0, _ => false
  | n + 1, w =>
      if w 0 = 3 then !oddEminus (Fin.tail w) else oddEminus (Fin.tail w)

@[simp] theorem oddEminus_cons {n : ℕ} (a : Fin 4) (w : Word n) :
    oddEminus (Fin.cons a w) = if a = 3 then !oddEminus w else oddEminus w := by
  simp [oddEminus]

theorem realSeed_transpose (a : Fin 4) :
    (realSeed a)ᵀ = if a = 3 then -realSeed a else realSeed a := by
  have hplus : Eplusᵀ = Eplus := SignedPermutation.e1_transpose
  have hminus : Eminusᵀ = -Eminus := SignedPermutation.e2_transpose
  fin_cases a <;> simp [realSeed, hplus, hminus, J1_transpose]

theorem realSeed_orthogonal (a : Fin 4) :
    (realSeed a)ᵀ * realSeed a = 1 := by
  have hplus : Eplusᵀ * Eplus = 1 := SignedPermutation.e1_orthogonal
  have hminus : Eminusᵀ * Eminus = 1 := SignedPermutation.e2_orthogonal
  fin_cases a <;> simp [realSeed, hplus, hminus, J1_transpose, J1_sq]

/-- The counted parity is the transpose sign of the actual native matrix. -/
theorem evaluate_transpose {n : ℕ} (w : Word n) :
    (evaluate w)ᵀ = if oddEminus w then -evaluate w else evaluate w := by
  induction n generalizing w with
  | zero => simp [evaluate, oddEminus]
  | succ n ih =>
      change (evaluate (Fin.tail w) ⊗ₖ realSeed (w 0))ᵀ =
        if oddEminus w then -(evaluate (Fin.tail w) ⊗ₖ realSeed (w 0))
        else evaluate (Fin.tail w) ⊗ₖ realSeed (w 0)
      rw [transpose_kronecker, ih, realSeed_transpose]
      by_cases h : w 0 = 3 <;>
        cases hp : oddEminus (Fin.tail w) <;>
        ext i j <;>
        simp [oddEminus, h, hp, Matrix.kroneckerMap_apply]

/-- Orthogonality is inherited factor by factor through the native product. -/
theorem evaluate_orthogonal {n : ℕ} (w : Word n) :
    (evaluate w)ᵀ * evaluate w = 1 := by
  induction n generalizing w with
  | zero => simp [evaluate]
  | succ n ih =>
      change (evaluate (Fin.tail w) ⊗ₖ realSeed (w 0))ᵀ *
        (evaluate (Fin.tail w) ⊗ₖ realSeed (w 0)) = 1
      rw [transpose_kronecker, ← Matrix.mul_kronecker_mul, ih,
        realSeed_orthogonal, Matrix.one_kronecker_one]

theorem evaluate_ne_zero {n : ℕ} (w : Word n) : evaluate w ≠ 0 := by
  intro h
  have hunit := evaluate_orthogonal w
  rw [h, Matrix.transpose_zero, zero_mul] at hunit
  exact zero_ne_one hunit

/-- Over the real carrier the two transpose signs cannot describe one word. -/
theorem evaluate_ne_neg {n : ℕ} (w : Word n) : evaluate w ≠ -evaluate w := by
  intro h
  apply evaluate_ne_zero w
  ext i j
  have hij := congrArg (fun M : Mat n => M i j) h
  change evaluate w i j = -(evaluate w i j) at hij
  change evaluate w i j = 0
  linarith

/-- Cardinality of the actual parity subtype; `false` means symmetric sign. -/
def wordCount (n : ℕ) (b : Bool) : ℕ :=
  Fintype.card {w : Word n // oddEminus w = b}

theorem wordCount_eq_sum (n : ℕ) (b : Bool) :
    wordCount n b = ∑ w : Word n, if oddEminus w = b then 1 else 0 := by
  rw [wordCount, Fintype.card_subtype, Finset.card_filter]

@[simp] theorem wordCount_zero_false : wordCount 0 false = 1 := by
  simp [wordCount_eq_sum, oddEminus, Word]

@[simp] theorem wordCount_zero_true : wordCount 0 true = 0 := by
  simp [wordCount_eq_sum, oddEminus, Word]

/-- Three head letters retain the sign; the fourth reverses it. -/
theorem wordCount_succ (n : ℕ) (b : Bool) :
    wordCount (n + 1) b = 3 * wordCount n b + wordCount n (!b) := by
  rw [wordCount_eq_sum,
    ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 4)).sum_comp
      (fun w => if oddEminus w = b then (1 : ℕ) else 0),
    Fintype.sum_prod_type]
  change (∑ a : Fin 4, ∑ w : Word n,
    if oddEminus (Fin.cons a w) = b then 1 else 0) = _
  rw [Fin.sum_univ_four]
  cases b <;>
    simp [oddEminus_cons, wordCount_eq_sum, Bool.not_eq_true_eq_eq_false,
      Bool.not_eq_false_eq_eq_true] <;> omega

theorem symmetricWordCount_succ (n : ℕ) :
    wordCount (n + 1) false = 3 * wordCount n false + wordCount n true :=
  wordCount_succ n false

theorem skewWordCount_succ (n : ℕ) :
    wordCount (n + 1) true = wordCount n false + 3 * wordCount n true := by
  simpa [add_comm] using wordCount_succ n true

/-- The two parity subtypes exhaust the four-letter word family. -/
theorem wordCount_total (n : ℕ) :
    wordCount n false + wordCount n true = 4 ^ n := by
  rw [wordCount_eq_sum, wordCount_eq_sum, ← Finset.sum_add_distrib]
  calc
    (∑ w : Word n,
        ((if oddEminus w = false then 1 else 0) +
          (if oddEminus w = true then 1 else 0))) =
        ∑ _w : Word n, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro w _
      cases oddEminus w <;> simp
    _ = 4 ^ n := by simp [Word, Fintype.card_fun]

/-- A positive equality expresses the parity imbalance without subtraction. -/
theorem symmetricWordCount_eq_skew_add (n : ℕ) :
    wordCount n false = wordCount n true + 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [wordCount_succ]
      change 3 * wordCount n false + wordCount n true =
        (3 * wordCount n true + wordCount n false) + 2 ^ (n + 1)
      rw [ih, pow_succ]
      ring

theorem symmetricWordCount_two : wordCount 2 false = 10 := by
  norm_num [wordCount_succ]

theorem skewWordCount_two : wordCount 2 true = 6 := by
  norm_num [wordCount_succ]

end InfoGeometry.Clifford.Cl11TensorTransposeCensus
