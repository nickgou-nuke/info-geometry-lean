import InfoGeometry.Canonical.IBMeasure
import InfoGeometry.KL.Measure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option linter.unusedSimpArgs false

open MeasureTheory
open scoped ENNReal

namespace IBFreeEnergy

open InfoGeometry.Canonical.IBMeasure

variable {T : Type*} [MeasurableSpace T]

/-- Canonical measure-theoretic KL divergence in `ℝ≥0∞`. -/
noncomputable abbrev klDivENN (μ ν : Measure T) : ℝ≥0∞ :=
  InfoGeometry.KL.kl_div μ ν

/--
Real-valued KL divergence, only available once finiteness has been established explicitly.
-/
noncomputable def klDiv (μ ν : Measure T) (_hfin : klDivENN μ ν ≠ ⊤) : ℝ :=
  (klDivENN μ ν).toReal

@[simp] lemma klDivENN_self (μ : Measure T) [SigmaFinite μ] :
    klDivENN μ μ = 0 := by
  simp [klDivENN, InfoGeometry.KL.klDiv_self]

lemma klDiv_nonneg (μ ν : Measure T) (hfin : klDivENN μ ν ≠ ⊤) :
    0 ≤ klDiv μ ν hfin := by
  exact ENNReal.toReal_nonneg

section Local

variable {X : Type*} [MeasurableSpace X] [Nonempty T]
variable (qT : Measure T) [IsProbabilityMeasure qT]
variable (β : ℝ) (D : X → T → ℝ) (x : X)

/-- Log-partition function for the local Gibbs slice. -/
noncomputable def IBLogPartition : ℝ :=
  Real.log (ENNReal.toReal (IBPartitionFunction qT β D x))

/-- Local free-energy functional for a candidate encoder slice. -/
noncomputable def IBLocalFreeEnergy
    (pT_given_x : ProbabilityMeasure T)
    (hKL : klDivENN (pT_given_x : Measure T) qT ≠ ⊤) : ℝ :=
  β * (∫ t, D x t ∂(pT_given_x : Measure T))
    + klDiv (pT_given_x : Measure T) qT hKL

end Local

end IBFreeEnergy
