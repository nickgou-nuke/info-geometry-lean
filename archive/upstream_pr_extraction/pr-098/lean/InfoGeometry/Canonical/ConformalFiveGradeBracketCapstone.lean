/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.ConformalFiveGradeBracketAPI

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.ConformalFiveGradeBracketAPI
open InfoGeometry.OperatorAlgebra.WeylWeightBalance

/-- Canonical projection capstone for the five-grade conformal bracket engine. -/
theorem conformal_five_grade_bracket_canonical_capstone
    (R : Type*) [Ring R] :
    let P := FiveGradeBracketPacket.canonicalUnitFiveGradeBracketPacket R
    -- 1. Grade compatibility: gradeCarrier.gradeOf = toWeylGrade (grade)
    (∀ x : Unit, P.gradeCarrier.gradeOf x = toWeylGrade (P.closure.inversion.grade x)) ∧
    -- 2. Bracket additivity
    IsAdditiveWeightForBracket P.gradeCarrier P.gradeCarrier P.bracket ∧
    -- 3. Balanced inputs bracket to physical grade zero
    (∀ x y : Unit, IsWeylBalanced P.gradeCarrier x y → IsPhysicalGradeZero P.gradeCarrier (P.bracket x y)) := by
  intro P
  exact ⟨
    P.gradeCompat,
    P.bracket_additive,
    fun x y h => bracket_is_physical_of_balanced P.gradeCarrier P.gradeCarrier P.bracket P.bracket_additive h
  ⟩

end InfoGeometry.Canonical
