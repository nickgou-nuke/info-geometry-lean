import InfoGeometry.Canonical.CanonicalZornCompositionTriality
import InfoGeometry.Canonical.CanonicalZornFiveGradedClosure
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
import InfoGeometry.Canonical.ZornCore

/-!
# Typed composition triality over the concrete five-grading

This owner reattaches the typed triality carriers from
`CanonicalZornCompositionTriality` to the maintained concrete five-graded and
projective owners:

* vectors land in the translation block of grade `+1`;
* positive semispinors land in the second grade `+1` block;
* negative semispinors land in the special-conformal block of grade `-1`;
* real split Zorn inputs are complexified into the typed vector carrier; and
* the composition-algebra Clifford relation is stated together with the proved
  projective null lift and grade-membership facts.

This still does not claim a full real spin-group action. That belongs in a
separate real-spin attachment owner.
-/

noncomputable section

namespace CanonicalZornCompositionFiveGradeBridge

open InfoGeometry.Canonical.CanonicalZornCompositionTriality
open InfoGeometry.Canonical.CanonicalZornFiveGradedClosure
open InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
open InfoGeometry.Canonical.TKKJordanPairData

/-- The vector copy placed in the translation block of grade `+1`. -/
def vectorGradePlus (V : Vector8) : ConformalMatrix :=
  zornPositive V.val

/-- The positive semispinor copy placed in the second grade `+1` block. -/
def spinorPlusGradePlus (S : SpinorPlus8) : ConformalMatrix :=
  zornPositiveSource S.val

/-- The negative semispinor copy placed in the special-conformal block of
grade `-1`. -/
def spinorMinusGradeMinus (C : SpinorMinus8) : ConformalMatrix :=
  zornNegative C.val

theorem vectorGradePlus_mem (V : Vector8) :
    vectorGradePlus V ∈ conformalGrade TKKGrade.p1 := by
  exact zornPositive_mem V.val

theorem spinorPlusGradePlus_mem (S : SpinorPlus8) :
    spinorPlusGradePlus S ∈ conformalGrade TKKGrade.p1 := by
  exact zornPositiveSource_mem S.val

theorem spinorMinusGradeMinus_mem (C : SpinorMinus8) :
    spinorMinusGradeMinus C ∈ conformalGrade TKKGrade.m1 := by
  exact zornNegative_mem C.val

/-- A real split Zorn vector, complexified into the typed vector carrier. -/
def realVector8 (X : ZornCore.Zorn) : Vector8 :=
  ⟨coreToCanonical X⟩

theorem realVector8_val (X : ZornCore.Zorn) :
    (realVector8 X).val = coreToCanonical X := rfl

/-- Capstone connecting the genuine three-carrier composition triality to the
concrete five-graded matrix closure and the `(5,5)` projective null lift.

This states only the proved composition-algebra Clifford action; it does not
assert that a `Spin(4,4)` group action has been constructed. -/
theorem composition_triality_five_grade_projective_bridge
    (X : ZornCore.Zorn) (S : SpinorPlus8) :
    conformalVectorQuadratic (zornProjectiveVector X) = 0 ∧
    vectorGradePlus (realVector8 X) ∈ conformalGrade TKKGrade.p1 ∧
    spinorPlusGradePlus S ∈ conformalGrade TKKGrade.p1 ∧
    spinorMinusGradeMinus (cliffordPlus (realVector8 X) S) ∈
      conformalGrade TKKGrade.m1 ∧
    (cliffordMinus (realVector8 X) (cliffordPlus (realVector8 X) S)).val =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornSmul
        (InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm (coreToCanonical X)) S.val := by
  exact ⟨zornProjectiveVector_null X, vectorGradePlus_mem _,
    spinorPlusGradePlus_mem _, spinorMinusGradeMinus_mem _,
    cliffordMinus_plus (realVector8 X) S⟩

end CanonicalZornCompositionFiveGradeBridge

end noncomputable section
