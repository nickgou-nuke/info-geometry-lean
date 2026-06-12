import Mathlib

/-!
# Cuntz-Krieger Primon Dynamics

Finite symbolic-dynamics core for the next layer:

* Fibonacci/Penrose adjacency matrix `A = [[1,1],[1,0]]`;
* the forbidden transition is the thin-thin transition;
* `A² = A + I`, the finite algebraic seed of Fibonacci growth;
* the golden ratio is the Perron root of `x² - x - 1`;
* finite word counts satisfy the Fibonacci recurrence.

This is not a full Cuntz-Krieger C*-algebra construction.  It is the
checkable adjacency/partition skeleton that such a construction uses.
-/

noncomputable section

open Matrix

def fibonacciAdj : Matrix (Fin 2) (Fin 2) ℕ :=
  !![1, 1;
     1, 0]

def fibonacciAdjInt : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1;
     1, 0]

def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

def allowedTransition (i j : Fin 2) : Prop :=
  fibonacciAdj i j = 1

def wordCount (n : ℕ) : ℕ :=
  Nat.fib (n + 2)

def finitePrimonPartition (β : ℝ) (n : ℕ) : ℝ :=
  (wordCount n : ℝ) * Real.exp (-(n : ℝ) * β)

theorem fibonacciAdj_sq :
    fibonacciAdj * fibonacciAdj = fibonacciAdj + 1 := by
  native_decide

theorem fibonacciAdjInt_det :
    fibonacciAdjInt.det = -1 := by
  native_decide

theorem allowed_00 : allowedTransition 0 0 := by
  simp [allowedTransition, fibonacciAdj]

theorem allowed_01 : allowedTransition 0 1 := by
  simp [allowedTransition, fibonacciAdj]

theorem allowed_10 : allowedTransition 1 0 := by
  simp [allowedTransition, fibonacciAdj]

theorem forbidden_11 : ¬ allowedTransition 1 1 := by
  simp [allowedTransition, fibonacciAdj]

theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have h5 : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  calc
    ((1 + Real.sqrt 5) / 2) ^ 2 =
        (1 + 2 * Real.sqrt 5 + Real.sqrt 5 ^ 2) / 4 := by ring
    _ = (1 + 2 * Real.sqrt 5 + 5) / 4 := by rw [h5]
    _ = (1 + Real.sqrt 5) / 2 + 1 := by ring

theorem goldenRatio_perron_polynomial :
    goldenRatio ^ 2 - goldenRatio - 1 = 0 := by
  rw [goldenRatio_sq]
  ring

theorem wordCount_recurrence (n : ℕ) :
    wordCount (n + 2) = wordCount (n + 1) + wordCount n := by
  unfold wordCount
  change Nat.fib (n + 4) = Nat.fib (n + 3) + Nat.fib (n + 2)
  rw [show n + 4 = (n + 2) + 2 by omega]
  rw [Nat.fib_add_two]
  rw [show n + 2 + 1 = n + 3 by omega]
  ac_rfl

theorem finitePrimonPartition_zero (β : ℝ) :
    finitePrimonPartition β 0 = 1 := by
  simp [finitePrimonPartition, wordCount]

/-- Finite Cuntz-Krieger/Primon package: Fibonacci adjacency, forbidden
    transition, Perron polynomial, and finite partition recurrence. -/
theorem cuntz_krieger_primon_synthesis :
    fibonacciAdj * fibonacciAdj = fibonacciAdj + 1 ∧
    fibonacciAdjInt.det = -1 ∧
    allowedTransition 0 0 ∧
    allowedTransition 0 1 ∧
    allowedTransition 1 0 ∧
    ¬ allowedTransition 1 1 ∧
    goldenRatio ^ 2 - goldenRatio - 1 = 0 ∧
    (∀ n, wordCount (n + 2) = wordCount (n + 1) + wordCount n) ∧
    (∀ β, finitePrimonPartition β 0 = 1) := by
  exact ⟨fibonacciAdj_sq, fibonacciAdjInt_det, allowed_00, allowed_01,
    allowed_10, forbidden_11, goldenRatio_perron_polynomial,
    wordCount_recurrence, finitePrimonPartition_zero⟩
