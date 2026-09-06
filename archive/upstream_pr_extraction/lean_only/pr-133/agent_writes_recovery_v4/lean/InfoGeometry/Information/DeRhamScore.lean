import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Real

/-- 
The logarithmic derivative of the partition function Q represents the closed 1-form score function.
q = d log Q = dQ / Q
-/
theorem score_as_de_rham_potential (Q : ℝ → ℝ) (x : ℝ)
    (hQ : DifferentiableAt ℝ Q x) (hQ_ne : Q x ≠ 0) :
    deriv (fun y => log (Q y)) x = deriv Q x / Q x := by
  have hd : HasDerivAt (fun y => log (Q y)) ((Q x)⁻¹ * deriv Q x) x :=
    (hasDerivAt_log hQ_ne).comp x hQ.hasDerivAt
  rw [hd.deriv]
  ring
