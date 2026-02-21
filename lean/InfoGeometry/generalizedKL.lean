import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators

/--
Generalized (unnormalized) KL divergence on a finite type, with convention
`0 * log(0 / x) = 0` implemented by branching on `μ a = 0`.

Note: This is only mathematically faithful to KL if `ν a > 0` whenever `μ a > 0`.
-/
noncomputable def generalizedKL {α : Type*} [Fintype α]
    (μ ν μ₀ : α → ℝ) : ℝ :=
  ∑ a : α, (
    (if μ a = 0 then 0
     else μ a * (Real.log (μ a / μ₀ a) - Real.log (ν a / μ₀ a)))
      + (ν a - μ a))

def μ_example : Fin 3 → ℝ := fun a => match a.val with
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | _ => 0

def ν_example : Fin 3 → ℝ := fun a => match a.val with
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | _ => 0

def μ₀_example : Fin 3 → ℝ := fun _ => 1

-- #eval generalizedKL μ_example ν_example μ₀_example
-- evaluation disabled because `Real.log` is noncomputable
