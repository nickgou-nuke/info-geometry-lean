import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Sandbox restore: de Rham score packet

Sandbox-only refactor of the small logarithmic-derivative packet. This keeps the
surface small and splits the statement into reusable derivative lemmas.

It records the finite calculus fact behind the score/de Rham readout:
`d(log Q) = dQ / Q` at points where `Q` is differentiable and nonzero.
-/

open Real

namespace Sandbox.Restore.DeRhamScore

/-- Helper derivative statement for the logarithm of a nonvanishing scalar field. -/
lemma hasDerivAt_log_comp
    (Q : ℝ → ℝ) (x : ℝ)
    (hQ : DifferentiableAt ℝ Q x) (hQ_ne : Q x ≠ 0) :
    HasDerivAt (fun y => log (Q y)) ((Q x)⁻¹ * deriv Q x) x := by
  exact (hasDerivAt_log hQ_ne).comp x hQ.hasDerivAt

/-- Derivative readout of the logarithmic score potential. -/
lemma deriv_log_comp
    (Q : ℝ → ℝ) (x : ℝ)
    (hQ : DifferentiableAt ℝ Q x) (hQ_ne : Q x ≠ 0) :
    deriv (fun y => log (Q y)) x = (Q x)⁻¹ * deriv Q x := by
  exact (hasDerivAt_log_comp Q x hQ hQ_ne).deriv

/--
The logarithmic derivative of the partition function `Q` gives the local score
readout `d log Q = dQ / Q`.
-/
theorem score_as_de_rham_potential
    (Q : ℝ → ℝ) (x : ℝ)
    (hQ : DifferentiableAt ℝ Q x) (hQ_ne : Q x ≠ 0) :
    deriv (fun y => log (Q y)) x = deriv Q x / Q x := by
  rw [deriv_log_comp Q x hQ hQ_ne]
  field_simp [hQ_ne]
  ring

end Sandbox.Restore.DeRhamScore
