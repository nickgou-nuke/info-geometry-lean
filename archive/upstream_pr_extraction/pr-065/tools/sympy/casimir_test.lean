import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

open Matrix

def MassSquaredCasimir (P : Fin 4 → ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  dotProduct P (mulVec g P)

theorem mass_squared_rest_frame (m : ℝ) :
    let P : Fin 4 → ℝ := fun i => if i = 0 then m else 0
    let g : Matrix (Fin 4) (Fin 4) ℝ := 
      fun i j => if i = 0 ∧ j = 0 then 1 else (if i = j then -1 else 0)
    MassSquaredCasimir P g = m^2 := by
  intro P g
  dsimp [MassSquaredCasimir, P, g, mulVec, dotProduct]
  rw [Fin.sum_univ_four]
  simp
  ring
