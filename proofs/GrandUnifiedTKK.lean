import InfoGeometry.Canonical.TKKJordanPairData

/-!
# Compatibility surface for the canonical TKK grade owner

The former version of this file bundled an assumed five-graded carrier with
unit-valued mirror, instanton, and “unification” records.  Those records did
not construct a TKK Lie algebra and were not used by the downstream grading
bridges.  The maintained owner is `TKKJordanPairData`, which supplies the
grade type, grade arithmetic, and five-graded Lie-algebra interface.

This file keeps only the old grade names and forwards them to that owner.
-/

namespace GrandUnifiedTKK

abbrev TKK_Grade := TKKJordanPairData.TKKGrade

namespace TKK_Grade

abbrev g_neg2 : TKK_Grade := TKKJordanPairData.TKKGrade.m2
abbrev g_neg1 : TKK_Grade := TKKJordanPairData.TKKGrade.m1
abbrev g_0 : TKK_Grade := TKKJordanPairData.TKKGrade.z0
abbrev g_1 : TKK_Grade := TKKJordanPairData.TKKGrade.p1
abbrev g_2 : TKK_Grade := TKKJordanPairData.TKKGrade.p2

end TKK_Grade

open TKK_Grade

def add_grade (i j : TKK_Grade) : Option TKK_Grade :=
  TKKJordanPairData.gradeAdd i j

@[simp] theorem add_grade_zero_left (i : TKK_Grade) :
    add_grade g_0 i = some i :=
  TKKJordanPairData.gradeAdd_z0_left i

@[simp] theorem add_grade_zero_right (i : TKK_Grade) :
    add_grade i g_0 = some i :=
  TKKJordanPairData.gradeAdd_z0_right i

theorem add_grade_m1_p1 :
    add_grade g_neg1 g_1 = some g_0 :=
  TKKJordanPairData.gradeAdd_m1_p1

theorem add_grade_m2_p2 :
    add_grade g_neg2 g_2 = some g_0 :=
  TKKJordanPairData.gradeAdd_m2_p2

abbrev FiveGradedLieAlgebra (R : Type*) [CommRing R] :=
  TKKJordanPairData.FiveGradedLieAlgebra R

end GrandUnifiedTKK
