import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

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

/--
Complex logarithmic derivative of a partition function on the principal-branch domain.
This is the complex `d log Q = dQ / Q` readout; the slit-plane hypothesis is the
branch condition for `Complex.log`, not a topological winding theorem.
-/
theorem complex_score_as_de_rham_potential (Q : ℂ → ℂ) (z : ℂ)
    (hQ : DifferentiableAt ℂ Q z) (hslit : Q z ∈ Complex.slitPlane) :
    deriv (fun w => Complex.log (Q w)) z = deriv Q z / Q z := by
  exact (hQ.hasDerivAt.clog hslit).deriv
