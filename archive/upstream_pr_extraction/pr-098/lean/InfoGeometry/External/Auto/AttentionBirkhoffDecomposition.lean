import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

/-- 
  The absolute formalization of the Attention Matrix / Birkhoff Polytope decomposition.
  A continuous doubly stochastic matrix (the thermodynamic Softmax output) is
  exactly a convex combination of discrete permutation matrices (the vertices).
-/

def P_id : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0],
    ![0, 1]]

def P_swap : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1],
    ![1, 0]]

def AttentionMatrix (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![x, 1 - x],
    ![1 - x, x]]

theorem attention_is_birkhoff_convex_combination (x : ℝ) :
    AttentionMatrix x = x • P_id + (1 - x) • P_swap := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [AttentionMatrix, P_id, P_swap]

theorem attention_weights_sum_to_one (x : ℝ) :
    x + (1 - x) = 1 := by
  ring
