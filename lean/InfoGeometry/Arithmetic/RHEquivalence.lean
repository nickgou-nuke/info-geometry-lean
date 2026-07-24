import InfoGeometry.Analysis.BregmanAnalyticBound
import Mathlib.Analysis.Complex.Basic

/-!
# Dikin positivity and RH-equivalence socket

This module proves the elementary positivity of the Dikin envelope.  It does
not prove any equivalence with the Riemann Hypothesis, Fredholm determinants, or
Möbius summatory bounds; future equivalences must be routed through the
Hestenes--Krein/categorical-colimit owner layer.
-/

open Complex

namespace InfoGeometry.Arithmetic.RHEquivalence

open InfoGeometry.Analysis.BregmanAnalyticBound

theorem dikinOmega_pos (t : ℝ) (ht : 0 < t) : 0 < dikinOmega t := by
  unfold dikinOmega
  have htne : t ≠ 0 := ne_of_gt ht
  have hexp0 : t + 1 < Real.exp t := Real.add_one_lt_exp htne
  have hexp : 1 + t < Real.exp t := by
    simpa [add_comm] using hexp0
  have hpos : 0 < 1 + t := by
    linarith
  have hlog0 : Real.log (1 + t) < Real.log (Real.exp t) := Real.log_lt_log hpos hexp
  have hlog : Real.log (1 + t) < t := by
    simpa [Real.log_exp] using hlog0
  linarith

/-- Statement shape for any future RH-equivalence theorem.  The required
categorical-colimit bridges are explicit inputs rather than hidden assumptions. -/
def rhEquivalenceStatement (RH fredholm mobius : Prop) : Prop :=
  (RH ↔ fredholm) ∧ (RH ↔ mobius)

end InfoGeometry.Arithmetic.RHEquivalence
