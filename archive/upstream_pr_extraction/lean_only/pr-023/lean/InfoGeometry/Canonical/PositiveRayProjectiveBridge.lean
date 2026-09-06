import InfoGeometry.MeasureProjective
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge

/-!
# InfoGeometry.Canonical.PositiveRayProjectiveBridge

Compatibility layer from the strictly positive full-support slice to the widened
projective-state substrate.

This file does not introduce a new quotient semantics. It records that
`PositiveRay` objects canonically land in the broader `ProjectiveState` world,
and that the wide projective logarithmic generator specializes to the pointwise
relative modular potential on the strict-positive slice.
-/

namespace InfoGeometry.Canonical.PositiveRayProjectiveBridge

open MeasureTheory
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.MeasureProjective
open InfoGeometry.MeasureProjective.ProjectiveState
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativePotentialDiscreteBridge

universe u

section FiniteDiscrete

variable {α : Type u}
variable [Fintype α] [Nonempty α]
variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- Canonical embedding of a full-support positive ray into the widened projective substrate. -/
noncomputable abbrev positiveRayToProjectiveState (q : PositiveRay α) : ProjectiveState α :=
  toProjectiveState (α := α) q

omit [Countable α] in
@[simp] theorem positiveRayToProjectiveState_normalize_eq
    (q : PositiveRay α) :
    normalize (positiveRayToProjectiveState (α := α) q)
      = pmfToProbMeasure (gaugeSectionFinProb (α := α) q) := by
  exact normalize_toProjectiveState (α := α) q

/-- On the strict-positive slice, the wide projective generator matches the relative modular potential a.e. -/
theorem positiveRay_logGenerator_eq_relativeModularPotential_ae
    (q q0 : PositiveRay α) :
    logGenerator
        (positiveRayToProjectiveState (α := α) q0)
        (positiveRayToProjectiveState (α := α) q)
      =ᶠ[ae (gaugeSectionFinProb (α := α) q).toMeasure]
        fun a => relativeModularPotential (α := α) q q0 a := by
  exact projectiveLogGenerator_eq_relativeModularPotential_ae (α := α) (q := q) (q0 := q0)

/-- On the strict-positive slice, the wide projective generator matches the relative modular potential pointwise. -/
theorem positiveRay_logGenerator_eq_relativeModularPotential
    (q q0 : PositiveRay α) (a : α) :
    logGenerator
        (positiveRayToProjectiveState (α := α) q0)
        (positiveRayToProjectiveState (α := α) q) a
      = relativeModularPotential (α := α) q q0 a := by
  exact projectiveLogGenerator_eq_relativeModularPotential (α := α) (q := q) (q0 := q0) a

end FiniteDiscrete

end InfoGeometry.Canonical.PositiveRayProjectiveBridge
