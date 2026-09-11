import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Measure-theoretic log potential

`rn_potential μ ν` is the negative log-likelihood ratio, i.e. `-llr μ ν`.
This is the canonical projective potential before quotienting by constants.
-/

namespace InfoGeometry.Measure

open MeasureTheory
open InfoGeometry
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- Negative log-likelihood ratio: `-llr μ ν`. -/
noncomputable def rn_potential (μ ν : Measure α) : α → ℝ :=
  fun x => -MeasureTheory.llr μ ν x

@[simp] lemma rn_potential_eq_potential (μ ν : Measure α) :
    rn_potential (μ := μ) (ν := ν) = InfoGeometry.potential μ ν := rfl

lemma measurable_rn_potential (μ ν : Measure α) :
    Measurable (rn_potential (μ := μ) (ν := ν)) := by
  simpa [rn_potential, InfoGeometry.potential] using
    (InfoGeometry.measurable_potential (μ := μ) (ν := ν))

section Gauge

variable {μ ν : Measure α}
variable [IsFiniteMeasure μ] [μ.HaveLebesgueDecomposition ν]
lemma rn_potential_smul_left_ae
    (hμν : μ.AbsolutelyContinuous ν)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ⊤) :
    rn_potential (μ := c • μ) (ν := ν)
      =ᵐ[μ] fun x => rn_potential (μ := μ) (ν := ν) x - Real.log c.toReal := by
  simpa [rn_potential, InfoGeometry.potential] using
    (InfoGeometry.potential_smul_left_ae (μ := μ) (ν := ν) hμν c hc hc_ne_top)

lemma rn_potential_smul_right_ae
    (hμν : μ.AbsolutelyContinuous ν)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ⊤) :
    rn_potential (μ := μ) (ν := c • ν)
      =ᵐ[μ] fun x => rn_potential (μ := μ) (ν := ν) x + Real.log c.toReal := by
  simpa [rn_potential, InfoGeometry.potential] using
    (InfoGeometry.potential_smul_right_ae (μ := μ) (ν := ν) hμν c hc hc_ne_top)

end Gauge

end InfoGeometry.Measure
