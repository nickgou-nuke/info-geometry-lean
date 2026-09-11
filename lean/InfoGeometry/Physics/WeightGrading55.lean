import InfoGeometry.Physics.OrbitClassification55
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# 5-slot weight packets for the `J₂(𝕆_s)` coordinate model

This file records a finite weight-labeled coordinate packet for the
`JordanMatrix10D` carrier together with a local orbit-type predicate.  It does
**not** construct a global Kantor--Koecher--Tits grading, a Lie-closure theorem,
or a classification theorem for the full split Albert geometry.

The weight labels and orbit names are bookkeeping devices for the named
coordinates used in this file.
-/

open InfoGeometry.Physics.OrbitClassification55
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace InfoGeometry.Physics.WeightGrading55

namespace JordanMatrix10D

/-! ## 1. 5-graded components -/

/-- The weight -2 component: ⟨ξ₊⟩. -/
def weightMinusTwo (X : JordanMatrix10D) : ℚ := X.xp

/-- The weight +2 component: ⟨ξ₋⟩. -/
def weightPlusTwo (X : JordanMatrix10D) : ℚ := X.xm

/-- The weight -1 component: the octonionic coordinate Z ∈ 𝕆_s. -/
def weightMinusOne (X : JordanMatrix10D) : SplitOct := X.z

/-- The weight +1 component: conj(Z) (same octonion, by Hermiticity). -/
def weightPlusOne (X : JordanMatrix10D) : SplitOct := X.z

/--
A finite record of the five weight slots used in the local `J₂(𝕆_s)` socket.

This is only a coordinate packet: it records the pieces named by the grading,
but does not claim any Lie-bracket closure or global TKK theorem.
-/
structure WeightCoordinates where
  minusTwo : ℚ
  minusOne : SplitOct
  zeroWeight : ℚ
  plusOne : SplitOct
  plusTwo : ℚ
  deriving Repr

/-- The local five-slot coordinate packet attached to `X`. -/
def weightCoordinates (X : JordanMatrix10D) : WeightCoordinates :=
  { minusTwo := weightMinusTwo X
    minusOne := weightMinusOne X
    zeroWeight := 0
    plusOne := weightPlusOne X
    plusTwo := weightPlusTwo X }

@[simp] theorem weightCoordinates_minusTwo (X : JordanMatrix10D) :
    (weightCoordinates X).minusTwo = X.xp := rfl

@[simp] theorem weightCoordinates_minusOne (X : JordanMatrix10D) :
    (weightCoordinates X).minusOne = X.z := rfl

@[simp] theorem weightCoordinates_zero (X : JordanMatrix10D) :
    (weightCoordinates X).zeroWeight = 0 := rfl

@[simp] theorem weightCoordinates_plusOne (X : JordanMatrix10D) :
    (weightCoordinates X).plusOne = X.z := rfl

@[simp] theorem weightCoordinates_plusTwo (X : JordanMatrix10D) :
    (weightCoordinates X).plusTwo = X.xm := rfl

/-- The local coordinate packet reconstructs the original named weight slots. -/
theorem weightCoordinates_eta (X : JordanMatrix10D) :
    weightCoordinates X =
      { minusTwo := X.xp
        minusOne := X.z
        zeroWeight := 0
        plusOne := X.z
        plusTwo := X.xm } := rfl

/-! ## 2. Refined orbit types under the 5-grading -/

/--
Refined orbit types that account for the conformal-weight grading.

- `isZero`:       X = 0 (all weights zero)
- `isPureNull`:   det = 0, X ≠ 0, and at least one outer weight slot
                  (`weightMinusTwo` or `weightPlusTwo`) vanishes.
- `isMixedNull`:  det = 0, X ≠ 0, and both outer weight slots are nonzero.
- `isGeneric`:    det ≠ 0.
-/
inductive RefinedOrbitType (X : JordanMatrix10D) : Prop where
  | isZero : X = JordanMatrix10D.zero → RefinedOrbitType X
  | isPureNull : X ≠ zero → X.det = 0 → (weightMinusTwo X = 0 ∨ weightPlusTwo X = 0) → RefinedOrbitType X
  | isMixedNull : X ≠ zero → X.det = 0 → (weightMinusTwo X ≠ 0 ∧ weightPlusTwo X ≠ 0) → RefinedOrbitType X
  | isGeneric : X.det ≠ 0 → RefinedOrbitType X

/--
The refined orbit classification refines the coarse `isZero ∨ isNull ∨ isGeneric`.
-/
theorem refined_orbit_classification (X : JordanMatrix10D) : RefinedOrbitType X := by
  by_cases hzero : X = JordanMatrix10D.zero
  · exact RefinedOrbitType.isZero hzero
  · by_cases hdet : X.det = 0
    · by_cases hminus : weightMinusTwo X = 0
      · exact RefinedOrbitType.isPureNull hzero hdet (Or.inl hminus)
      · by_cases hplus : weightPlusTwo X = 0
        · exact RefinedOrbitType.isPureNull hzero hdet (Or.inr hplus)
        · exact RefinedOrbitType.isMixedNull hzero hdet ⟨hminus, hplus⟩
    · exact RefinedOrbitType.isGeneric hdet

/-! ## 3. Connection to the Fioresi et al. E/Ē decomposition -/

/--
The lightcone decomposition of Cs = ℚ·E ⊕ ℚ·Ē generalizes to the
split octonions via the Zorn norm.  For a spinor Z ∈ 𝕆_s, the
E-component is `a + b` (the trace) and the Ē-component is `a - b`
(the difference), where `Z = (a, x; y, b)` in Zorn coordinates.
-/
def eComponent (Z : SplitOct) : ℚ := (Z.a : ℚ) + (Z.b : ℚ)

def ebComponent (Z : SplitOct) : ℚ := (Z.a : ℚ) - (Z.b : ℚ)

end JordanMatrix10D

end InfoGeometry.Physics.WeightGrading55
