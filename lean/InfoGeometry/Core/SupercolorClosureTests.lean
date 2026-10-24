/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SupercolorMatrixUnitBridge

/-! Narrow test surface. No changes to the repository-wide test aggregator. -/
namespace InfoGeometryTests.SupercolorClosure

open InfoGeometry.Core.SuperGrassmannianSusy
open InfoGeometry.Core.SupercolorSourceClosure
open InfoGeometry.Core.SupercolorMatrixExamples
open InfoGeometry.Core.SupercolorMatrixUnitBridge

#check @colorBoson_mul_middle
#check @colorBoson_mul_of_common_source
#check @colorBoson_lieBracket_of_common_source
#check @common_absorption_iff_equal_corange
#check @colorBoson_odd_actions
#check @odd_pair_closure
#check @graded_jacobi
#check @superJacobi_even_odd_odd
#check @superJacobi_odd_odd_odd
#check @star_colorBoson_of_dual
#check @total_charge_star_of_mp
#check @colorEmbeddingHom
#check @colorEmbedding_injective
#check @colorEmbedding_single
#check @orthogonal_not_common_absorption
#check @fin2_orthogonal_extended_susy_certificate
#check @fin4_orthogonal_extended_susy_certificate
#check @fin2_noncommutative_star_certificate
#check @fin4_noncommutative_star_certificate

example : lieBracket (colorBoson (forward (ι := Fin 2)) backward 0 1)
    (forward 1) = forward 0 := by
  simpa using (common_source_odd_actions (ι := Fin 2) 0 1 1).1

example : colorBoson (forward (ι := Fin 4)) backward 0 1 ≠ 0 :=
  colorBoson_ne_zero 0 1

example : colorBoson (orthogonalForward (ι := Fin 4)) orthogonalBackward 0 1 = 0 := by
  simp [orthogonal_colorBoson_eq_diagonal]

example : ¬ (orthogonalForward (0 : Fin 2) *
    (orthogonalBackward 1 * orthogonalForward 1) = orthogonalForward 0) :=
  orthogonal_not_common_absorption (by decide)

end InfoGeometryTests.SupercolorClosure
