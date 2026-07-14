import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.WeylA2CancellationChart

/-!
# InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow

Finite alternating determinant shadow in the three-node `A₂` lane.

This file isolates the explicit alternating-factor structure that should come
before any genuine three-node divisibility theorem:

* scalar denominator factor:
  `(y - x) * (z - x) * (z - y)`,
* exponential numerator factor:
  `(exp y - exp x) * (exp z - exp x) * (exp z - exp y)`,
* both factors negate under the basic transposition `x ↔ y`.
-/

namespace WeylA2AlternatingDeterminantShadow

open InfoGeometry.Canonical.WeylA2CancellationChart

open scoped Matrix

abbrev Chart := InfoGeometry.Canonical.WeylA2CancellationChart.A2Chart

namespace Chart

variable (C : Chart)

/-- The explicit scalar Vandermonde factor in the `A₂` lane. -/
@[rep_depth thermo]
def alternatingDenominatorFactor : ℝ :=
  (C.y - C.x) * (C.z - C.x) * (C.z - C.y)

/-- The explicit exponential Vandermonde factor in the `A₂` lane. -/
@[rep_depth thermo]
noncomputable def alternatingNumeratorFactor : ℝ :=
  (Real.exp C.y - Real.exp C.x) *
    (Real.exp C.z - Real.exp C.x) *
    (Real.exp C.z - Real.exp C.y)

/-- Swap the first two nodes. -/
@[rep_depth thermo]
def swap01 : Chart where
  x := C.y
  y := C.x
  z := C.z

/-- Swapping `x` and `y` negates the scalar alternating factor. -/
@[rep_depth thermo]
theorem alternatingDenominatorFactor_swap01_eq_neg :
    C.swap01.alternatingDenominatorFactor = -C.alternatingDenominatorFactor := by
  unfold alternatingDenominatorFactor swap01
  ring

/-- Swapping `x` and `y` negates the exponential alternating factor. -/
@[rep_depth thermo]
theorem alternatingNumeratorFactor_swap01_eq_neg :
    C.swap01.alternatingNumeratorFactor = -C.alternatingNumeratorFactor := by
  unfold alternatingNumeratorFactor swap01
  ring

/-- Hence the determinant denominator is alternating under the basic transposition. -/
@[rep_depth thermo]
theorem denominator_swap01_eq_neg :
    C.swap01.alternatingDenominatorFactor = -C.alternatingDenominatorFactor :=
  C.alternatingDenominatorFactor_swap01_eq_neg

/-- Hence the determinant numerator is alternating under the basic transposition. -/
@[rep_depth thermo]
theorem numerator_swap01_eq_neg :
    C.swap01.alternatingNumeratorFactor = -C.alternatingNumeratorFactor :=
  C.alternatingNumeratorFactor_swap01_eq_neg

/-- Combined three-node alternating determinant packet. -/
@[rep_depth thermo]
theorem alternating_determinant_packet :
    C.swap01.alternatingDenominatorFactor = -C.alternatingDenominatorFactor
    ∧ C.swap01.alternatingNumeratorFactor = -C.alternatingNumeratorFactor := by
  exact ⟨C.denominator_swap01_eq_neg, C.numerator_swap01_eq_neg⟩

end Chart

end WeylA2AlternatingDeterminantShadow
