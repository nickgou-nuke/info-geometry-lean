import InfoGeometry.MeasureProjective
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace InfoGeometry.MeasureProjective.Normalized

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### 1. Normalized slice of the cone -/

/-- Canonical projection from a nonzero unnormalized state to the probability slice. -/
noncomputable def normalizedSlice [Nonempty α] (μ : NonzeroUState α) : ProbabilityMeasure α :=
  μ.1.normalize

/-- Embed a `ProbabilityMeasure` into the unnormalized finite-measure cone. -/
abbrev probMeasureToUState (P : ProbabilityMeasure α) : UState α :=
  P.toFiniteMeasure

/-- A probability measure is nonzero when viewed as a finite measure. -/
@[simp] theorem probMeasureToUState_ne_zero (P : ProbabilityMeasure α) :
    probMeasureToUState P ≠ 0 := by
  simpa [probMeasureToUState] using
    (ProbabilityMeasure.toFiniteMeasure_nonzero P)

/-- The canonical injection from `ProbabilityMeasure` to `NonzeroUState`. -/
abbrev probMeasureToNonzero (P : ProbabilityMeasure α) : NonzeroUState α :=
  ⟨probMeasureToUState P, probMeasureToUState_ne_zero P⟩

/-- Normalizing an embedded probability measure recovers it exactly. -/
@[simp] theorem normalizedSlice_probMeasureToNonzero [Nonempty α]
    (P : ProbabilityMeasure α) :
    normalizedSlice (probMeasureToNonzero P) = P := by
  simpa [normalizedSlice, probMeasureToNonzero, probMeasureToUState] using
    (ProbabilityMeasure.toFiniteMeasure_normalize_eq_self P)

/-- Register a probability measure as a projective ray. -/
noncomputable def probMeasureToProjectiveState [Nonempty α]
    (P : ProbabilityMeasure α) : ProjectiveState α :=
  Quotient.mk (sameRaySetoid (α := α)) (probMeasureToNonzero P)

@[simp] theorem normalize_probMeasureToProjectiveState [Nonempty α]
    (P : ProbabilityMeasure α) :
    ProjectiveState.normalize (probMeasureToProjectiveState P) = P := by
  simpa [probMeasureToProjectiveState] using
    normalizedSlice_probMeasureToNonzero (P := P)

/-! ### 2. PMF embedding and discrete equivalence -/

/-- Canonical embedding of a `PMF` into `ProbabilityMeasure`. -/
noncomputable abbrev pmfToProbMeasure (P : PMF α) : ProbabilityMeasure α :=
  ⟨P.toMeasure, inferInstance⟩

/-- Register a `PMF` as a normalized projective ray. -/
noncomputable def pmfToProjectiveState [Nonempty α] (P : PMF α) : ProjectiveState α :=
  probMeasureToProjectiveState (pmfToProbMeasure P)

@[simp] theorem normalize_pmfToProjectiveState [Nonempty α] (P : PMF α) :
    ProjectiveState.normalize (pmfToProjectiveState P) = pmfToProbMeasure P := by
  simpa [pmfToProjectiveState] using
    normalize_probMeasureToProjectiveState (P := pmfToProbMeasure P)

section Countable

variable [Countable α]

/-- Recover a `PMF` from a discrete probability measure. -/
noncomputable def probMeasureToPMF (P : ProbabilityMeasure α) : PMF α :=
  ((P : Measure α)).toPMF

@[simp] theorem probMeasureToPMF_apply (P : ProbabilityMeasure α) (x : α) :
    probMeasureToPMF P x = (P : Measure α) {x} := by
  simpa [probMeasureToPMF] using
    (Measure.toPMF_apply (μ := (P : Measure α)) x)

/-- `PMF → ProbabilityMeasure → PMF` is the identity on the discrete slice. -/
@[simp] theorem probMeasureToPMF_pmfToProbMeasure (P : PMF α) :
    probMeasureToPMF (pmfToProbMeasure P) = P := by
  change P.toMeasure.toPMF = P
  simpa [probMeasureToPMF, pmfToProbMeasure] using
    (PMF.toMeasure_toPMF (p := P))

/-- `ProbabilityMeasure → PMF → ProbabilityMeasure` is the identity on countable
measurable-singleton spaces. -/
@[simp] theorem pmfToProbMeasure_probMeasureToPMF (P : ProbabilityMeasure α) :
    pmfToProbMeasure (probMeasureToPMF P) = P := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((P : Measure α)).toPMF.toMeasure) = (P : Measure α)
  simpa [probMeasureToPMF, pmfToProbMeasure] using
    (Measure.toPMF_toMeasure (μ := (P : Measure α)))

end Countable

/-! ### 3. Log-potential on the PMF slice -/

/-- On the PMF slice, `logPotential` is exactly the negative log of the RN derivative. -/
@[simp] theorem logPotential_pmf_eq_log_rnDeriv
    {P Q : PMF α} :
    logPotential P.toMeasure Q.toMeasure
      = fun x => - Real.log ((P.toMeasure.rnDeriv Q.toMeasure x).toReal) := rfl

/-- The self log-potential vanishes almost everywhere on the PMF slice. -/
@[simp] theorem logPotential_pmf_self_ae (P : PMF α) :
    logPotential P.toMeasure P.toMeasure =ᶠ[ae P.toMeasure] 0 := by
  filter_upwards [MeasureTheory.llr_self P.toMeasure] with x hx
  change -MeasureTheory.llr P.toMeasure P.toMeasure x = 0
  simp [hx]

end InfoGeometry.MeasureProjective.Normalized
