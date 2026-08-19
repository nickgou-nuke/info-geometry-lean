import InfoGeometry.Analysis.BregmanAnalyticBound
import Mathlib.Analysis.Complex.Basic

/-!
# Dikin positivity

This module contains the elementary analytic inequality only.  RH
equivalences belong to their concrete zeta or spectral owners.
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

end InfoGeometry.Arithmetic.RHEquivalence
