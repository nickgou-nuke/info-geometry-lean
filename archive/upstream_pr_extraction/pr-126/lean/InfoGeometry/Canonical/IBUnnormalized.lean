import InfoGeometry.Canonical.IBUpdate
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# InfoGeometry.Canonical.IBUnnormalized

Canonical unnormalized finite-measure realization of discrete IB score fields.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.IB

variable {T : Type} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

/-- Finite-valued discrete score fields have finite total mass. -/
private lemma tsum_ne_top_of_fintype
    (f : T → ℝ≥0∞) (hfTop : ∀ t, f t ≠ ⊤) :
    (∑' t, f t) ≠ ⊤ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun t _ => hfTop t)

/-- Counting-measure realization of a discrete score field. -/
private theorem isFiniteMeasure_discreteScore
    (f : T → ℝ≥0∞) (hfTop : ∀ t, f t ≠ ⊤) :
    IsFiniteMeasure (Measure.count.withDensity f) := by
  refine MeasureTheory.isFiniteMeasure_withDensity ?_
  rw [MeasureTheory.lintegral_count]
  exact tsum_ne_top_of_fintype f hfTop

/--
Unnormalized finite-measure realization of a discrete score field.
-/
noncomputable def discreteScoreMeasure
    (f : T → ℝ≥0∞) (hfTop : ∀ t, f t ≠ ⊤) : FiniteMeasure T :=
  ⟨Measure.count.withDensity f, isFiniteMeasure_discreteScore f hfTop⟩

@[simp] theorem discreteScoreMeasure_toMeasure
    (f : T → ℝ≥0∞) (hfTop : ∀ t, f t ≠ ⊤) :
    ((discreteScoreMeasure f hfTop : FiniteMeasure T) : Measure T)
      = Measure.count.withDensity f := rfl

@[simp] theorem discreteScoreMeasure_apply_singleton
    (f : T → ℝ≥0∞) (hfTop : ∀ t, f t ≠ ⊤) (t : T) :
    ((discreteScoreMeasure f hfTop : Measure T) {t}) = f t := by
  rw [discreteScoreMeasure_toMeasure]
  rw [withDensity_apply f (measurableSet_singleton t)]
  rw [MeasureTheory.lintegral_singleton]
  simp

@[simp] theorem ennreal_discreteScoreMeasure_mass
    (f : T → ℝ≥0∞) (hfTop : ∀ t, f t ≠ ⊤) :
    (((discreteScoreMeasure f hfTop).mass : ℝ≥0∞)) = ∑' t, f t := by
  rw [FiniteMeasure.ennreal_mass, discreteScoreMeasure_toMeasure]
  rw [withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]
  exact MeasureTheory.lintegral_count f

theorem discreteScoreMeasure_ne_zero_of_tsum_ne_zero
    (f : T → ℝ≥0∞) (hfTop : ∀ t, f t ≠ ⊤)
    (hf0 : (∑' t, f t) ≠ 0) :
    discreteScoreMeasure f hfTop ≠ 0 := by
  have hmass :
      (discreteScoreMeasure f hfTop).mass ≠ 0 := by
    rw [← ENNReal.coe_ne_zero, ennreal_discreteScoreMeasure_mass]
    exact hf0
  exact (FiniteMeasure.mass_nonzero_iff _).1 hmass

section IB

variable {X Y : Type} [Fintype X] [Fintype Y]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- Unnormalized frozen BA score as a finite measure on the target alphabet. -/
noncomputable def baScoreFrozenMeasure
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) : FiniteMeasure T :=
  discreteScoreMeasure
    (baScoreFrozen prob qT mY_givenT x)
    (baScoreFrozen_ne_top prob qT mY_givenT x)

/-- Unnormalized intrinsic BA score as a finite measure on the target alphabet. -/
noncomputable def baScoreMeasure
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) : FiniteMeasure T :=
  discreteScoreMeasure
    (ibBlahutArimotoStepUnnormalized prob pT_givenX x)
    (fun t => by
      simpa [ibBlahutArimotoStepUnnormalized, baScore_eq_baScoreFrozen_induced] using
        baScoreFrozen_ne_top
          (prob := prob)
          (qT := inducedMarginalT prob pT_givenX)
          (mY_givenT := inducedMProjection prob pT_givenX)
          (x := x) (t := t))

@[simp] theorem baScoreFrozenMeasure_apply_singleton
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) (t : T) :
    ((baScoreFrozenMeasure prob qT mY_givenT x : Measure T) {t})
      = baScoreFrozen prob qT mY_givenT x t :=
  discreteScoreMeasure_apply_singleton
    (baScoreFrozen prob qT mY_givenT x)
    (baScoreFrozen_ne_top prob qT mY_givenT x) t

@[simp] theorem baScoreMeasure_apply_singleton
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) (t : T) :
    ((baScoreMeasure prob pT_givenX x : Measure T) {t})
      = ibBlahutArimotoStepUnnormalized prob pT_givenX x t :=
  discreteScoreMeasure_apply_singleton
    (ibBlahutArimotoStepUnnormalized prob pT_givenX x)
    (fun t => by
      simpa [ibBlahutArimotoStepUnnormalized, baScore_eq_baScoreFrozen_induced] using
        baScoreFrozen_ne_top
          (prob := prob)
          (qT := inducedMarginalT prob pT_givenX)
          (mY_givenT := inducedMProjection prob pT_givenX)
          (x := x) (t := t))
    t

@[simp] theorem ennreal_baScoreFrozenMeasure_mass
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    (((baScoreFrozenMeasure prob qT mY_givenT x).mass : ℝ≥0∞))
      = ∑' t, baScoreFrozen prob qT mY_givenT x t :=
  ennreal_discreteScoreMeasure_mass
    (baScoreFrozen prob qT mY_givenT x)
    (baScoreFrozen_ne_top prob qT mY_givenT x)

@[simp] theorem ennreal_baScoreMeasure_mass
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    (((baScoreMeasure prob pT_givenX x).mass : ℝ≥0∞))
      = ∑' t, ibBlahutArimotoStepUnnormalized prob pT_givenX x t :=
  ennreal_discreteScoreMeasure_mass
    (ibBlahutArimotoStepUnnormalized prob pT_givenX x)
    (fun t => by
      simpa [ibBlahutArimotoStepUnnormalized, baScore_eq_baScoreFrozen_induced] using
        baScoreFrozen_ne_top
          (prob := prob)
          (qT := inducedMarginalT prob pT_givenX)
          (mY_givenT := inducedMProjection prob pT_givenX)
          (x := x) (t := t))

theorem baScoreFrozenMeasure_ne_zero
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    baScoreFrozenMeasure prob qT mY_givenT x ≠ 0 :=
  discreteScoreMeasure_ne_zero_of_tsum_ne_zero
    (baScoreFrozen prob qT mY_givenT x)
    (baScoreFrozen_ne_top prob qT mY_givenT x)
    (baScoreFrozen_slice_ne_zero prob qT mY_givenT x)

theorem baScoreMeasure_ne_zero
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    baScoreMeasure prob pT_givenX x ≠ 0 :=
  discreteScoreMeasure_ne_zero_of_tsum_ne_zero
    (ibBlahutArimotoStepUnnormalized prob pT_givenX x)
    (fun t => by
      simpa [ibBlahutArimotoStepUnnormalized, baScore_eq_baScoreFrozen_induced] using
        baScoreFrozen_ne_top
          (prob := prob)
          (qT := inducedMarginalT prob pT_givenX)
          (mY_givenT := inducedMProjection prob pT_givenX)
          (x := x) (t := t))
    (ibBlahutArimotoScoreSlice prob pT_givenX x).nonzero

end IB

end InfoGeometry.Canonical.IB
