import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

noncomputable section

def partialDeriv (f : (Fin 4 → ℝ) → ℝ) (i : Fin 4) (q : Fin 4 → ℝ) : ℝ :=
  deriv (fun x => f (Function.update q i x)) (q i)

def Hessian (f : (Fin 4 → ℝ) → ℝ) (q : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => deriv (fun y => partialDeriv f i (Function.update q j y)) (q j)

def Psi (q : Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2)

/-!
Open debt: the native Lean calculus proof of `Hessian Psi q 0 0 = 1`
is intentionally not asserted in this scratch bridge.  The executable SymPy
lane owns the calculation until a kernel proof is written in the main
`lean/InfoGeometry` tree.
-/
