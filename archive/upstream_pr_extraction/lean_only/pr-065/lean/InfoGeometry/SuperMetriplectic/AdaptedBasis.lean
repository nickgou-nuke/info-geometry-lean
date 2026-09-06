import InfoGeometry.SuperMetriplectic.SupertraceBodyBridge
import InfoGeometry.Clifford.Grading

/-!
# Operator chiral block decomposition

The former scalar adapted-basis packets have been retired.  They supplied
coordinates and equalities as structure fields rather than constructing an
operator-level decomposition.  This file retains the genuine doubled-carrier
theorem that downstream operator geometry can use.
-/

namespace InfoGeometry.SuperMetriplectic

namespace DoubledChiralProjectorBridge

open InfoGeometry.Krein

section Doubled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/-- The canonical chiral projectors sum to the identity on the doubled carrier. -/
theorem grade_projectors_sum :
    gradePlusProj (E := E) + gradeMinusProj (E := E) =
      ContinuousLinearMap.id ℝ H₂ :=
  gradeProj_sum (E := E)

/-- The plus and minus projectors annihilate in the plus-minus order. -/
theorem grade_plus_comp_minus_zero :
    (gradePlusProj (E := E)).comp (gradeMinusProj (E := E)) = 0 :=
  gradePlusProj_comp_gradeMinusProj (E := E)

/-- The minus and plus projectors annihilate in the minus-plus order. -/
theorem grade_minus_comp_plus_zero :
    (gradeMinusProj (E := E)).comp (gradePlusProj (E := E)) = 0 :=
  gradeMinusProj_comp_gradePlusProj (E := E)

/-- Every continuous operator is the sum of its four genuine chiral blocks. -/
theorem operator_eq_sum_chiral_blocks
    (T : H₂ →L[ℝ] H₂) :
    (gradePlusProj (E := E)).comp (T.comp (gradePlusProj (E := E)))
      + (gradePlusProj (E := E)).comp (T.comp (gradeMinusProj (E := E)))
      + (gradeMinusProj (E := E)).comp (T.comp (gradePlusProj (E := E)))
      + (gradeMinusProj (E := E)).comp (T.comp (gradeMinusProj (E := E))) = T := by
  calc
    _ = (gradePlusProj (E := E) + gradeMinusProj (E := E)).comp
        (T.comp (gradePlusProj (E := E) + gradeMinusProj (E := E))) := by
          simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
          abel
    _ = (ContinuousLinearMap.id ℝ H₂).comp
        (T.comp (ContinuousLinearMap.id ℝ H₂)) := by
          rw [grade_projectors_sum]
    _ = T := by simp [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

end Doubled

end DoubledChiralProjectorBridge

end InfoGeometry.SuperMetriplectic
