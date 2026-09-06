import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Function.Basic

noncomputable section

def QuaternionicCoordinates := Fin 4 → ℝ

def Psi (q : QuaternionicCoordinates) : ℝ :=
  (1 / 2 : ℝ) * (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2)

def partialDeriv (f : (Fin 4 → ℝ) → ℝ) (i : Fin 4) (q : Fin 4 → ℝ) : ℝ :=
  deriv (fun x => f (Function.update q i x)) (q i)

def FisherRaoMetric (q : QuaternionicCoordinates) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => deriv (fun y => partialDeriv Psi i (Function.update q j y)) (q j)

theorem FisherRaoMetric_eq_one (q : QuaternionicCoordinates) :
    FisherRaoMetric q = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    dsimp [FisherRaoMetric, Psi, partialDeriv, Function.update]
    simp
  )
