import InfoGeometry.Physics.OrbitClassification55
import Mathlib.Tactic

/-!
# 5-graded weight decomposition of J₂(𝕆_s) and refined orbit classification

The 10D Jordan algebra J₂(𝕆_s) carries a natural 5-grading by conformal
weight inherited from the Kantor–Koecher–Tits construction:

    J₂ = 𝔤_{-2} ⊕ 𝔤_{-1} ⊕ 𝔤₀ ⊕ 𝔤₁ ⊕ 𝔤₂

* 𝔤_{±2} = the light-cone coordinates ⟨ξ₊, ξ₋⟩  (weight ±2)
* 𝔤_{±1} = the octonionic null cone 𝕆_s          (weight ±1)
* 𝔤₀     = the dilatation/scaling generator

Under this grading, the `isNull` orbit splits into three sub-types:

1. **pure null**: ξ₊ or ξ₋ vanishes, Z is zero-divisor in one direction
2. **mixed null**: both ξ₊ and ξ₋ non-zero, but det = 0
3. **totally null**: all components zero (isZero)

The Fioresi et al. ℂ_s decomposition `E = 1 + j` (weight +1) vs
`Ē = 1 - j` (weight -1) generalizes to 𝕆_s via the split-octonion
lightcone projectors.
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
- `isPureNull`:   det = 0, X ≠ 0, ALL weight components lie in a single
                  Z-divisor subspace (E or Ē direction in the Cs slice).
- `isMixedNull`:  det = 0, X ≠ 0, weights span both E and Ē directions.
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
