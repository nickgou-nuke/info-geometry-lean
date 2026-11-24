/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity

/-!
# Projective positive-ray `L¹` and information-geometric readouts

This bridge connects the canonical positive-ray gauge to the existing finite
simplex information-geometry owners.  It does not introduce a second quotient,
normalization, relative-potential, Fisher, or Csiszár implementation.

The carrier is a strictly positive projective ray.  Its canonical gauge gives
an interior probability vector, so the existing Amari/Csiszar and Fisher/Cramér–Rao
theorems apply without identifying an unnormalised representative with a state.
-/

noncomputable section

namespace InfoGeometry.Canonical.ProjectiveL1InformationGeometryBridge

open scoped BigOperators
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
open InfoGeometry.Epistemology.ChentsovMetricInvariance

universe u

section FiniteDiscrete

variable {α : Type u} [Fintype α] [Nonempty α]

/-- The canonical gauge of a positive ray, viewed as a simplex-interior state. -/
noncomputable def positiveRayToProbInterior (q : PositiveRay α) : ProbInterior α where
  p := gaugeSection (α := α) q
  pos := fun a => (gaugeSection (α := α) q).pos a
  sum_one := by
    simpa only [InfoGeometry.PositiveMeasure.Z_def] using
      (Z_gaugeSection (α := α) q)

@[simp] theorem positiveRayToProbInterior_apply
    (q : PositiveRay α) (a : α) :
    (positiveRayToProbInterior (α := α) q).p a = gaugeSection (α := α) q a := rfl

/-- The ordinary finite `L¹` distance between canonical representatives of two rays. -/
noncomputable def projectiveL1Distance (q q0 : PositiveRay α) : ℝ :=
  ∑ a, |gaugeSection (α := α) q a - gaugeSection (α := α) q0 a|

@[simp] theorem projectiveL1Distance_self (q : PositiveRay α) :
    projectiveL1Distance (α := α) q q = 0 := by
  simp only [projectiveL1Distance, sub_self, abs_zero, Finset.sum_const_zero]

theorem projectiveL1Distance_nonneg (q q0 : PositiveRay α) :
    0 ≤ projectiveL1Distance (α := α) q q0 := by
  unfold projectiveL1Distance
  exact Finset.sum_nonneg (fun a _ => abs_nonneg _)

theorem projectiveL1Distance_symm (q q0 : PositiveRay α) :
    projectiveL1Distance (α := α) q q0 =
      projectiveL1Distance (α := α) q0 q := by
  unfold projectiveL1Distance
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [abs_sub_comm]

/-- A projective ray has a canonical Amari `α`-divergence against another ray. -/
noncomputable def projectiveAmariAlphaDivergence
    (αParam : ℝ) (q q0 : PositiveRay α) : ℝ :=
  amariAlphaDivergence αParam
    (positiveRayToProbInterior (α := α) q).p
    (positiveRayToProbInterior (α := α) q0).p

theorem projectiveAmariAlphaDivergence_nonneg
    (αParam : ℝ) (q q0 : PositiveRay α) :
    0 ≤ projectiveAmariAlphaDivergence (α := α) αParam q q0 := by
  exact amariAlphaDivergence_nonneg αParam
    (positiveRayToProbInterior (α := α) q)
    (positiveRayToProbInterior (α := α) q0)

theorem projectiveAmariAlphaDivergence_dual
    (αParam : ℝ) (q q0 : PositiveRay α) :
    projectiveAmariAlphaDivergence (α := α) (-αParam) q q0 =
      projectiveAmariAlphaDivergence (α := α) αParam q0 q := by
  simpa [projectiveAmariAlphaDivergence] using
    (amariAlphaDivergence_dual
      αParam
      (positiveRayToProbInterior (α := α) q).p
      (positiveRayToProbInterior (α := α) q0).p)

theorem projectiveAmariAlphaDivergence_zero_eq_zero_iff
    (q q0 : PositiveRay α) :
    projectiveAmariAlphaDivergence (α := α) 0 q q0 = 0 ↔
      (positiveRayToProbInterior (α := α) q).p =
        (positiveRayToProbInterior (α := α) q0).p := by
  simpa [projectiveAmariAlphaDivergence] using
    (amariAlphaDivergence_zero_eq_zero_iff
      (positiveRayToProbInterior (α := α) q)
      (positiveRayToProbInterior (α := α) q0))

/-- The Fisher metric transported to the projective positive-ray chart. -/
noncomputable def projectiveFisherMetric (q : PositiveRay α)
    (u v : α → ℝ) : ℝ :=
  fisherMetric (positiveRayToProbInterior (α := α) q) u v

theorem projectiveFisherMetric_nonneg (q : PositiveRay α) (u : α → ℝ) :
    0 ≤ projectiveFisherMetric (α := α) q u u := by
  exact fisherMetric_nonneg (positiveRayToProbInterior (α := α) q) u

/-- On the canonical gauge, Fisher's quadratic form is the existing inverse-prior
`χ²` form, so the two readouts are not separate metrics. -/
theorem projectiveFisherMetric_eq_chiSquaredInner
    (q : PositiveRay α) (u : α → ℝ) :
    projectiveFisherMetric (α := α) q u u =
      InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge.chiSquaredInner
        (gaugeSection (α := α) q) u u := by
  rfl

end FiniteDiscrete

end InfoGeometry.Canonical.ProjectiveL1InformationGeometryBridge
