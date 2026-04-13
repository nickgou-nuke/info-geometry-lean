import InfoGeometry.Thermo.ModularKLDivergence
import InfoGeometry.Canonical.PositiveRayProjectiveBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ModularKLDivergenceBridge

Repo-native bridge surface for the modular/KL lane on the strict-positive
projective owners.

This file adds no new ontology. It only re-exports and lightly repackages:
- strict-positive generalized-KL scale/shape decomposition;
- projective logarithmic-generator compatibility with relative modular
  potential on `PositiveRay`;
- the equivalent negative-relative-log-density form.
-/

namespace InfoGeometry.Canonical.ModularKLDivergenceBridge

open scoped ENNReal NNReal
open MeasureTheory
open InfoGeometry.PositiveMeasure
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore

section ScaleShape

variable {α : Type*} [Fintype α]

/--
Strict-positive scale/shape split of generalized KL on rays:
projective (shape) term plus radial mass-gauge term.
-/
@[rep_depth projective]
theorem generalizedKL_scale_shape_split
    [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
    Z (α := α) (R := ℝ) μ
      * generalizedKL (α := α)
          (normalize (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) ν)
      + gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  simpa using
    InfoGeometry.Thermo.ModularKLDivergence.generalizedKL_scale_shape_split
      (α := α) μ ν

/-- Equivalent slack split: generalized KL = shape log-ratio part + radial mass slack. -/
@[rep_depth projective]
theorem generalizedKL_eq_klLike_add_massSlack
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
    klLike (α := α) μ ν +
      (Z (α := α) (R := ℝ) ν - Z (α := α) (R := ℝ) μ) := by
  exact generalizedKL_eq_klLike_add_Z (α := α) μ ν

/--
In the strict-positive cone, both scale/shape components in the generalized-KL
split are nonnegative.
-/
@[rep_depth projective]
theorem generalizedKL_scale_shape_terms_nonneg
    [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    0 ≤
        Z (α := α) (R := ℝ) μ
          * generalizedKL (α := α)
              (normalize (α := α) (R := ℝ) μ)
              (normalize (α := α) (R := ℝ) ν)
      ∧
    0 ≤ gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  constructor
  · exact mul_nonneg
      (le_of_lt (PositiveMeasure.Z_pos (α := α) (R := ℝ) μ))
      (PositiveMeasure.generalizedKL_nonneg
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν))
  · exact PositiveMeasure.gklTerm_nonneg
      (Z (α := α) (R := ℝ) μ)
      (Z (α := α) (R := ℝ) ν)
      (PositiveMeasure.Z_pos (α := α) (R := ℝ) μ)
      (PositiveMeasure.Z_pos (α := α) (R := ℝ) ν)

/--
Strict-positive mass mismatch gives strictly positive radial gauge term in the
scale/shape split.
-/
@[rep_depth projective]
theorem generalizedKL_scale_shape_mass_term_pos_of_mass_ne
    [Nonempty α]
    (μ ν : PositiveMeasure α ℝ)
    (hMass : Z (α := α) (R := ℝ) μ ≠ Z (α := α) (R := ℝ) ν) :
    0 < gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  exact PositiveMeasure.gklTerm_pos_of_ne
      (Z (α := α) (R := ℝ) μ)
      (Z (α := α) (R := ℝ) ν)
      (PositiveMeasure.Z_pos (α := α) (R := ℝ) μ)
      (PositiveMeasure.Z_pos (α := α) (R := ℝ) ν)
      hMass

/--
Combined closure package: scale/shape decomposition plus nonnegativity of both
components.
-/
@[rep_depth projective]
theorem generalizedKL_scale_shape_split_with_nonneg
    [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
        Z (α := α) (R := ℝ) μ
          * generalizedKL (α := α)
              (normalize (α := α) (R := ℝ) μ)
              (normalize (α := α) (R := ℝ) ν)
        + gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν)
      ∧
    0 ≤
        Z (α := α) (R := ℝ) μ
          * generalizedKL (α := α)
              (normalize (α := α) (R := ℝ) μ)
              (normalize (α := α) (R := ℝ) ν)
      ∧
    0 ≤ gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  refine ⟨generalizedKL_scale_shape_split (α := α) μ ν, ?_⟩
  exact generalizedKL_scale_shape_terms_nonneg (α := α) μ ν

end ScaleShape

section PositiveRayCompatibility

variable {α : Type*}
variable [Fintype α] [Nonempty α]
variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/--
On the strict-positive slice, the widened projective logarithmic generator is
almost everywhere the relative modular potential.
-/
@[rep_depth projective]
theorem positiveRay_logGenerator_eq_relativeModularPotential_ae
    (q q0 : PositiveRay α) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRayToProjectiveState
          (α := α) q0)
        (InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRayToProjectiveState
          (α := α) q)
      =ᶠ[ae (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.gaugeSectionFinProb
            (α := α) q).toMeasure]
        fun a => relativeModularPotential (α := α) q q0 a := by
  exact
    InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRay_logGenerator_eq_relativeModularPotential_ae
      (α := α) q q0

/--
Pointwise strict-positive compatibility: projective logarithmic generator equals
relative modular potential.
-/
@[rep_depth projective, simp]
theorem positiveRay_logGenerator_eq_relativeModularPotential
    (q q0 : PositiveRay α) (a : α) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRayToProjectiveState
          (α := α) q0)
        (InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRayToProjectiveState
          (α := α) q) a
      = relativeModularPotential (α := α) q q0 a := by
  exact
    InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRay_logGenerator_eq_relativeModularPotential
      (α := α) q q0 a

/--
Equivalent pointwise form: projective logarithmic generator equals the negative
relative log-density.
-/
@[rep_depth projective, simp]
theorem positiveRay_logGenerator_eq_neg_relativeLogDensity
    (q q0 : PositiveRay α) (a : α) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRayToProjectiveState
          (α := α) q0)
        (InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRayToProjectiveState
          (α := α) q) a
      = -relativeLogDensity (α := α) q q0 a := by
  rw [positiveRay_logGenerator_eq_relativeModularPotential (α := α) (q := q) (q0 := q0)
      (a := a)]
  exact relativeModularPotential_eq_neg_relativeLogDensity (α := α) q q0 a

end PositiveRayCompatibility

end InfoGeometry.Canonical.ModularKLDivergenceBridge
