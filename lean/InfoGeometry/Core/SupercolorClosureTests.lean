/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SupercolorMatrixUnitBridge
import InfoGeometry.Core.SupercolorSourceClosure

/-! Concrete common-source and disjoint-sector tests use different models. -/
namespace InfoGeometryTests.SupercolorClosure

open InfoGeometry.Core.SuperGrassmannianSusy
open InfoGeometry.Core.SupercolorSourceClosure
open InfoGeometry.Core.SupercolorMatrixExamples
open InfoGeometry.Core.SupercolorMatrixUnitBridge

#check @coexact_absorption_iff_equal
#check @colorBoson_lieBracket_of_common_source
#check @total_charge_star_of_mp
#check @colorEmbeddingHom
#check @colorEmbedding_injective
#check @colorEmbedding_star
#check @fin2_orthogonal_extended_susy_certificate
#check @fin4_orthogonal_extended_susy_certificate

example : lieBracket (colorBoson (forward (ι := Fin 2)) backward 0 1)
    (forward 1) = forward 0 := by
  have hq : ∀ i : Fin 2, backward i * forward i =
      Matrix.single none none (1 : ℝ) := by
    intro i
    simp [forward, backward]
  unfold lieBracket
  rw [colorBoson_mul_forward matrix_supercolor hq,
    forward_mul_colorBoson matrix_supercolor]
  simp

example : colorBoson (forward (ι := Fin 4)) backward 0 1 ≠ 0 :=
  colorBoson_ne_zero 0 1

example : colorBoson (orthogonalForward (ι := Fin 4)) orthogonalBackward 0 1 = 0 := by
  unfold colorBoson
  exact orthogonal_matrix_supercolor.d_mul_b_ne (by decide : (0 : Fin 4) ≠ 1)

example : ¬ (orthogonalForward (0 : Fin 2) *
    (orthogonalBackward 1 * orthogonalForward 1) = orthogonalForward 0) := by
  intro h
  have hz := (orthogonal_absorption_forces_zero
    orthogonal_matrix_supercolor (by decide : (0 : Fin 2) ≠ 1) h).1
  have he := congrArg (fun M => M (0, true) (0, false)) hz
  simp [orthogonalForward, Matrix.single] at he

example : colorEmbeddingHom (Matrix.single (0 : Fin 4) 1 (1 : ℝ)) =
    colorBoson forward backward 0 1 := colorEmbedding_single 0 1

end InfoGeometryTests.SupercolorClosure
