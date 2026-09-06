/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.ConformalFiveGradeBracketAPI

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.ConformalFiveGradeBracketAPI
open InfoGeometry.OperatorAlgebra.WeylWeightBalance

theorem conformal_five_grade_bracket_canonical_capstone
    {L ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (P : FiveGradeBracketPacket L ι R) :
    (∀ x : L, P.gradeCarrier.gradeOf x = toWeylGrade (P.closure.inversion.grade x)) ∧
    IsAdditiveWeightForBracket P.gradeCarrier P.gradeCarrier P.bracket ∧
    (∀ x y : L, IsWeylBalanced P.gradeCarrier x y →
      IsPhysicalGradeZero P.gradeCarrier (P.bracket x y)) := by
  exact ⟨P.gradeCompat, P.bracket_additive,
    fun x y h => bracket_is_physical_of_balanced P.gradeCarrier P.gradeCarrier
      P.bracket P.bracket_additive h⟩

end InfoGeometry.Canonical
