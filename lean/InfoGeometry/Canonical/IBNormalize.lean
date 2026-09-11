import InfoGeometry.Canonical.IBUnnormalized
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Measure.Normalized

/-!
# InfoGeometry.Canonical.IBNormalize

Canonical bridge from unnormalized finite score measures to normalized PMFs.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.IB

variable {T : Type} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

private theorem tsum_ne_top_of_fintype
    (f : T → ℝ≥0∞) (hfTop : ∀ t, f t ≠ ⊤) :
    (∑' t, f t) ≠ ⊤ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun t _ => hfTop t)

/--
Normalizing a discrete finite score measure recovers the canonical PMF
normalization.
-/
theorem probMeasureToPMF_normalize_discreteScoreMeasure
    [Nonempty T]
    (f : T → ℝ≥0∞)
    (hf0 : (∑' t, f t) ≠ 0)
    (hfTop : ∀ t, f t ≠ ⊤) :
    InfoGeometry.MeasureProjective.Normalized.probMeasureToPMF
      ((discreteScoreMeasure f hfTop).normalize)
      =
    PMF.normalize f hf0 (tsum_ne_top_of_fintype f hfTop) := by
  classical
  let μ := discreteScoreMeasure f hfTop
  have hμ : μ ≠ 0 := discreteScoreMeasure_ne_zero_of_tsum_ne_zero f hfTop hf0
  have hmass :
      (((μ.mass : ℝ≥0∞))) = ∑' t, f t := by
    simpa [μ] using ennreal_discreteScoreMeasure_mass f hfTop
  ext t
  rw [InfoGeometry.MeasureProjective.Normalized.probMeasureToPMF_apply]
  have hmassnz : μ.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff μ).2 hμ
  have hnorm :
      ((μ.normalize : Measure T) {t})
        =
      ((μ.mass : ℝ≥0∞))⁻¹ * ((μ : Measure T) {t}) := by
    have h :=
      congrArg (fun ν : Measure T => ν {t}) (μ.toMeasure_normalize_eq_of_nonzero hμ)
    simpa [Measure.coe_nnreal_smul_apply, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      FiniteMeasure.ennreal_mass, ENNReal.coe_inv hmassnz] using h
  rw [hnorm, hmass, discreteScoreMeasure_apply_singleton]
  rw [PMF.normalize_apply]
  ac_rfl

section IB

variable {X Y : Type} [Fintype X] [Fintype Y]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]

/--
The frozen BA step is the PMF normalization of its unnormalized finite-measure
score.
-/
theorem baScoreFrozenMeasure_normalize_eq_stepFrozen
    [Nonempty T]
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    InfoGeometry.MeasureProjective.Normalized.probMeasureToPMF
      ((baScoreFrozenMeasure prob qT mY_givenT x).normalize)
      =
    ibBlahutArimotoStepFrozen prob qT mY_givenT x := by
  simpa [baScoreFrozenMeasure, ibBlahutArimotoStepFrozen] using
    probMeasureToPMF_normalize_discreteScoreMeasure
      (f := baScoreFrozen prob qT mY_givenT x)
      (hf0 := baScoreFrozen_slice_ne_zero prob qT mY_givenT x)
      (hfTop := baScoreFrozen_ne_top prob qT mY_givenT x)

/--
The intrinsic BA step is the PMF normalization of its unnormalized finite-measure
score.
-/
theorem baScoreMeasure_normalize_eq_step
    [Nonempty T]
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    InfoGeometry.MeasureProjective.Normalized.probMeasureToPMF
      ((baScoreMeasure prob pT_givenX x).normalize)
      =
    ibBlahutArimotoStep prob pT_givenX x := by
  simpa [baScoreMeasure, ibBlahutArimotoStepUnnormalized,
    baScore_eq_baScoreFrozen_induced] using
    probMeasureToPMF_normalize_discreteScoreMeasure
      (f := ibBlahutArimotoStepUnnormalized prob pT_givenX x)
      (hf0 := (ibBlahutArimotoScoreSlice prob pT_givenX x).nonzero)
      (hfTop := fun t => by
        simpa [ibBlahutArimotoStepUnnormalized, baScore_eq_baScoreFrozen_induced] using
          baScoreFrozen_ne_top
            (prob := prob)
            (qT := inducedMarginalT prob pT_givenX)
            (mY_givenT := inducedMProjection prob pT_givenX)
            (x := x) (t := t))

end IB

end InfoGeometry.Canonical.IB
