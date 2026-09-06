import InfoGeometry.Algebra.Zorn.G2ParabolicLineCoordinateReadback
import InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient

/-!
# Structural interface for native parabolic line representatives

The named parabolic carriers do not form a three-distinct representative list:
`lineInfinity = lineOne` kernel-checks. Downstream code that needs exhaustive
coverage of `NativeLine` should therefore route through the quotient/surjective
candidate interface, not through the ad hoc trio `(lineZero, lineInfinity,
lineOne)`.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness

open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2ParabolicLineCoordinateReadback
open InfoGeometry.Algebra.Zorn.G2NativeLineSetQuotient

 theorem lineInfinity_eq_lineOne : lineInfinity = lineOne :=
  InfoGeometry.Algebra.Zorn.G2ParabolicLineCoordinateReadback.lineInfinity_eq_lineOne

theorem lineZero_ne_lineInfinity : lineZero ≠ lineInfinity :=
  InfoGeometry.Algebra.Zorn.G2ParabolicLineCoordinateReadback.lineZero_ne_lineInfinity

theorem lineZero_ne_lineOne : lineZero ≠ lineOne :=
  InfoGeometry.Algebra.Zorn.G2ParabolicLineCoordinateReadback.lineZero_ne_lineOne

theorem not_three_distinct_named_parabolic_lines :
    ¬ (lineZero ≠ lineInfinity ∧ lineInfinity ≠ lineOne ∧ lineZero ≠ lineOne) := by
  intro h
  exact h.2.1 lineInfinity_eq_lineOne

theorem nativeLine_candidate_surjective :
    Function.Surjective candidateLine :=
  candidateLine_surjective

noncomputable def nativeLineRepresentativeQuotientEquiv :
    nativeLineQuotient ≃ NativeLine :=
  lineSetQuotientToNativeLines

end InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness
