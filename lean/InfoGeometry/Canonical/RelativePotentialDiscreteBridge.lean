import InfoGeometry.Basic
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.MeasureProjective.GeneratorBridge

/-!
# InfoGeometry.Canonical.RelativePotentialDiscreteBridge

Discrete finite-slice representation of the projective/affine relative-potential
spine.

This file attaches the new `PositiveRayCore` / `RelativePotentialCore` root
language to the existing PMF / `MeasureProjective` presentation:
- canonical positive-ray gauge sections as `FinProb`
- induced projective states on the discrete measure slice
- identification of `ProjectiveState.logGenerator` with the relative modular
  potential
-/

open scoped BigOperators ENNReal

namespace RelativePotentialDiscreteBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.MeasureProjective
open InfoGeometry.MeasureProjective.Normalized
open MeasureTheory

universe u

section FiniteDiscrete

variable {α : Type u}
variable [Fintype α] [Nonempty α]
variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- Canonical finite-probability presentation of the positive-ray gauge section. -/
noncomputable def gaugeSectionFinProb (q : PositiveRay α) : InfoGeometry.FinProb α :=
  InfoGeometry.FinProb.of_fintype
    (fun a => ENNReal.ofReal (gaugeSection (α := α) q a))
    (by
      have hsum : ∑ a : α, gaugeSection (α := α) q a = (1 : ℝ) := by
        simpa only [InfoGeometry.PositiveMeasure.Z_def] using
          (Z_gaugeSection (α := α) q)
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · simpa only [ENNReal.ofReal_one] using congrArg ENNReal.ofReal hsum
      · intro a ha
        exact le_of_lt ((gaugeSection (α := α) q).pos a))

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
theorem gaugeSectionFinProb_apply
    (q : PositiveRay α) (a : α) :
    gaugeSectionFinProb (α := α) q a
      = ENNReal.ofReal (gaugeSection (α := α) q a) := by
  rfl

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
theorem gaugeSectionFinProb_apply_toReal
    (q : PositiveRay α) (a : α) :
    ((gaugeSectionFinProb (α := α) q a).toReal)
      = gaugeSection (α := α) q a := by
  rw [gaugeSectionFinProb_apply]
  exact ENNReal.toReal_ofReal (le_of_lt ((gaugeSection (α := α) q).pos a))

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
theorem gaugeSectionFinProb_apply_ne_zero
    (q : PositiveRay α) (a : α) :
    gaugeSectionFinProb (α := α) q a ≠ 0 := by
  rw [gaugeSectionFinProb_apply]
  intro hzero
  have hle : gaugeSection (α := α) q a ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
  exact ((gaugeSection (α := α) q).pos a).ne' (le_antisymm hle (le_of_lt ((gaugeSection (α := α) q).pos a)))

/-- Register a positive ray as a discrete projective state through its gauge slice. -/
noncomputable def toProjectiveState
    (q : PositiveRay α) : ProjectiveState α :=
  pmfToProjectiveState (gaugeSectionFinProb (α := α) q)

omit [Countable α] in
theorem normalize_toProjectiveState
    (q : PositiveRay α) :
    ProjectiveState.normalize (toProjectiveState (α := α) q)
      = pmfToProbMeasure (gaugeSectionFinProb (α := α) q) := by
  exact normalize_pmfToProjectiveState (gaugeSectionFinProb (α := α) q)

omit [Countable α] in
/-- The canonical discrete gauge slices are mutually absolutely continuous. -/
theorem gaugeSectionFinProb_absolutelyContinuous
    (q q0 : PositiveRay α) :
    (gaugeSectionFinProb (α := α) q).toMeasure.AbsolutelyContinuous
      (gaugeSectionFinProb (α := α) q0).toMeasure := by
  intro s hs0
  have hsEmpty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hsx : ({x} : Set α) ⊆ s := by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hx
    have hsingle_le :
        (gaugeSectionFinProb (α := α) q0).toMeasure ({x} : Set α)
          ≤ (gaugeSectionFinProb (α := α) q0).toMeasure s :=
      MeasureTheory.measure_mono hsx
    have hsingle_zero :
        (gaugeSectionFinProb (α := α) q0).toMeasure ({x} : Set α) = 0 := by
      have hsingle_le_zero := hsingle_le
      rw [hs0] at hsingle_le_zero
      exact le_antisymm hsingle_le_zero (zero_le _)
    have hsingle_eval :
        (gaugeSectionFinProb (α := α) q0).toMeasure ({x} : Set α)
          = gaugeSectionFinProb (α := α) q0 x := by
      exact PMF.toMeasure_apply_singleton
        (gaugeSectionFinProb (α := α) q0) x (measurableSet_singleton x)
    have hnonzero : gaugeSectionFinProb (α := α) q0 x ≠ 0 := by
      rw [gaugeSectionFinProb_apply]
      intro hzero
      have hle : gaugeSection (α := α) q0 x ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
      have hzero' : gaugeSection (α := α) q0 x = 0 :=
        le_antisymm hle (le_of_lt ((gaugeSection (α := α) q0).pos x))
      exact ((gaugeSection (α := α) q0).pos x).ne' hzero'
    rw [hsingle_eval] at hsingle_zero
    exact hnonzero hsingle_zero
  rw [hsEmpty]
  exact measure_empty

/--
On the finite discrete slice, the existing `MeasureProjective` logarithmic
generator is exactly the new relative modular potential.
-/
theorem projectiveLogGenerator_eq_relativeModularPotential_ae
    (q q0 : PositiveRay α) :
    ProjectiveState.logGenerator
        (toProjectiveState (α := α) q0)
        (toProjectiveState (α := α) q)
      =ᶠ[ae (gaugeSectionFinProb (α := α) q).toMeasure]
        fun a => relativeModularPotential (α := α) q q0 a := by
  let P : InfoGeometry.FinProb α := gaugeSectionFinProb (α := α) q
  let Q : InfoGeometry.FinProb α := gaugeSectionFinProb (α := α) q0
  have hgen :
      ProjectiveState.logGenerator
          (pmfToProjectiveState Q)
          (pmfToProjectiveState P)
        =ᶠ[ae P.toMeasure]
          fun a => -Real.log ((P a).toReal / (Q a).toReal) :=
    InfoGeometry.MeasureProjective.GeneratorBridge.logGenerator_pmf_eq_log_div P Q
      (gaugeSectionFinProb_absolutelyContinuous (α := α) q q0)
  have hgen' :
      ProjectiveState.logGenerator
          (toProjectiveState (α := α) q0)
          (toProjectiveState (α := α) q)
        =ᶠ[ae (gaugeSectionFinProb (α := α) q).toMeasure]
          fun a =>
            -Real.log (((gaugeSectionFinProb (α := α) q) a).toReal /
              ((gaugeSectionFinProb (α := α) q0) a).toReal) := by
    simpa only [P, Q, toProjectiveState] using hgen
  filter_upwards [hgen'] with a ha
  rw [gaugeSectionFinProb_apply_toReal (α := α) (q := q) (a := a),
      gaugeSectionFinProb_apply_toReal (α := α) (q := q0) (a := a)] at ha
  calc
    ProjectiveState.logGenerator
        (toProjectiveState (α := α) q0)
        (toProjectiveState (α := α) q) a
      = -Real.log (gaugeSection (α := α) q a / gaugeSection (α := α) q0 a) := ha
    _ = relativeModularPotential (α := α) q q0 a := by
      rw [relativeModularPotential_eq_logDensity_base_sub_logDensity]
      unfold InfoGeometry.Canonical.PositiveRayCore.logDensity
      rw [Real.log_div
        ((gaugeSection (α := α) q).pos a).ne'
        ((gaugeSection (α := α) q0).pos a).ne']
      ring

/--
On the finite full-support discrete slice, the projective logarithmic generator
agrees pointwise with the relative modular potential.
-/
theorem projectiveLogGenerator_eq_relativeModularPotential
    (q q0 : PositiveRay α) (a : α) :
    ProjectiveState.logGenerator
        (toProjectiveState (α := α) q0)
        (toProjectiveState (α := α) q) a
      = relativeModularPotential (α := α) q q0 a := by
  have hfg :=
    projectiveLogGenerator_eq_relativeModularPotential_ae (α := α) (q := q) (q0 := q0)
  rw [Filter.EventuallyEq, ae_iff] at hfg
  by_contra hneq
  have hs :
      ({a} : Set α) ⊆
        {x |
          ¬ProjectiveState.logGenerator
              (toProjectiveState (α := α) q0)
              (toProjectiveState (α := α) q) x
            = relativeModularPotential (α := α) q q0 x} := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hneq
  have hsingle_le_zero :
      (gaugeSectionFinProb (α := α) q).toMeasure ({a} : Set α) ≤ 0 := by
    calc
      (gaugeSectionFinProb (α := α) q).toMeasure ({a} : Set α)
          ≤ (gaugeSectionFinProb (α := α) q).toMeasure
              {x |
                ¬ProjectiveState.logGenerator
                    (toProjectiveState (α := α) q0)
                    (toProjectiveState (α := α) q) x
                  = relativeModularPotential (α := α) q q0 x} :=
            MeasureTheory.measure_mono hs
      _ = 0 := hfg
  have hsingle_zero :
      (gaugeSectionFinProb (α := α) q).toMeasure ({a} : Set α) = 0 :=
    le_antisymm hsingle_le_zero (zero_le _)
  have hsingle_eval :
      (gaugeSectionFinProb (α := α) q).toMeasure ({a} : Set α)
        = gaugeSectionFinProb (α := α) q a := by
    exact PMF.toMeasure_apply_singleton
      (gaugeSectionFinProb (α := α) q) a (measurableSet_singleton a)
  rw [hsingle_eval] at hsingle_zero
  exact gaugeSectionFinProb_apply_ne_zero (α := α) q a hsingle_zero

end FiniteDiscrete

end RelativePotentialDiscreteBridge
