import InfoGeometry.MeasureProjective
import InfoGeometry.Measure.DiscreteRN
import InfoGeometry.Measure.Normalized
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

set_option autoImplicit false

namespace InfoGeometry.MeasureProjective.GeneratorBridge

open MeasureTheory
open InfoGeometry.MeasureProjective
open InfoGeometry.Measure.DiscreteRN
open InfoGeometry.MeasureProjective.Normalized

variable {α : Type*} [MeasurableSpace α] [Countable α] [Nonempty α] [MeasurableSingletonClass α]

/--
On the PMF slice, the projective logarithmic generator evaluates almost everywhere
to the negative log-ratio of the probability mass functions.
-/
theorem logGenerator_pmf_eq_log_div (P Q : PMF α)
    [P.toMeasure.HaveLebesgueDecomposition Q.toMeasure]
    (hPQ : P.toMeasure.AbsolutelyContinuous Q.toMeasure) :
    ProjectiveState.logGenerator (pmfToProjectiveState Q) (pmfToProjectiveState P)
      =ᶠ[ae P.toMeasure] fun x => - Real.log ((P x).toReal / (Q x).toReal) := by
  have h_rn := rnDeriv_pmf_eq_div P Q hPQ
  filter_upwards [h_rn] with x hx_rn
  unfold ProjectiveState.logGenerator logPotential
  simp only [ProjectiveState.logGenerator_mk, normalize_pmfToProjectiveState, pmfToProbMeasure,
    ProbabilityMeasure.coe_mk]
  rw [MeasureTheory.llr_def]
  simp only [Pi.neg_apply, hx_rn]
  rw [ENNReal.toReal_div]

end InfoGeometry.MeasureProjective.GeneratorBridge
