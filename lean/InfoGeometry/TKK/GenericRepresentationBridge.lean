import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Honest grading contract for a future TKK/Freudenthal representation. -/
namespace InfoGeometry.TKK.GenericRepresentation
open InfoGeometry.Algebra

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

structure GradedRepresentation (K : LieActionLane R A) where
  sourceGrade : K.L → ℤ
  targetGrade : Module.End R A → ℤ
  targetGrade_map : ∀ x, targetGrade (K.act x) = sourceGrade x

namespace GradedRepresentation
variable {K : LieActionLane R A} (ρ : GradedRepresentation K)

theorem preserves_grade (x : K.L) :
    ρ.targetGrade (K.act x) = ρ.sourceGrade x := ρ.targetGrade_map x

theorem map_bracket (x y : K.L) :
    K.act ⁅x, y⁆ = ⁅K.act x, K.act y⁆ := by
  exact K.act.map_lie x y

end GradedRepresentation

structure FiveGradeRepresentation (K : LieActionLane R A) where
  repr : GradedRepresentation K
  sourceInRange : ∀ x, repr.sourceGrade x ∈ ({-2, -1, 0, 1, 2} : Set ℤ)

namespace FiveGradeRepresentation
variable {K : LieActionLane R A} (ρ : FiveGradeRepresentation K)

theorem map_bracket (ρ : FiveGradeRepresentation K) (x y : K.L) :
    K.act ⁅x, y⁆ = ⁅K.act x, K.act y⁆ :=
  K.act.map_lie x y

theorem preserves_grade (x : K.L) :
  ρ.1.targetGrade (K.act x) = ρ.1.sourceGrade x :=
  GradedRepresentation.preserves_grade ρ.1 x
end FiveGradeRepresentation
end InfoGeometry.TKK.GenericRepresentation
