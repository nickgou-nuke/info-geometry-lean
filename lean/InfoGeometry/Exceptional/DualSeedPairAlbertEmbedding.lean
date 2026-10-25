/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedPeirce
import InfoGeometry.Algebra.H3ZornCubicNormStructure
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Exceptional.Freudenthal

noncomputable section

namespace InfoGeometry.Exceptional.DualSeedPairAlbertEmbedding

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.Freudenthal

@[simp] theorem h3zorn_add_def (X Y : H3Zorn ℝ) :
    X + Y = ⟨X.α₁ + Y.α₁, X.α₂ + Y.α₂, X.α₃ + Y.α₃,
              ZornVectorMatrix.add X.a Y.a,
              ZornVectorMatrix.add X.b Y.b,
              ZornVectorMatrix.add X.c Y.c⟩ := rfl

@[simp] theorem h3zorn_smul_def (r : ℝ) (X : H3Zorn ℝ) :
    r • X = ⟨r * X.α₁, r * X.α₂, r * X.α₃,
              ZornVectorMatrix.smul r X.a,
              ZornVectorMatrix.smul r X.b,
              ZornVectorMatrix.smul r X.c⟩ := rfl

noncomputable def cuntzToAlbert_e1 : H3Zorn ℝ :=
  ⟨1, 0, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

noncomputable def cuntzToAlbert_e2 : H3Zorn ℝ :=
  ⟨0, 1, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

noncomputable def cuntzToAlbert_e3 : H3Zorn ℝ :=
  ⟨0, 0, 1, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

noncomputable def cuntzToAlbert_Q1 : H3Zorn ℝ :=
  ⟨0, 0, 0, ZornVectorMatrix.one, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

noncomputable def jordanProduct (X Y : H3Zorn ℝ) : H3Zorn ℝ := X * Y

theorem linearTrace_diagonal {α₁ α₂ α₃ : ℝ} :
    linearTrace ⟨α₁, α₂, α₃, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩ =
      α₁ + α₂ + α₃ := by
  simp [linearTrace]

theorem adjointQuad_e1_zero : adjointQuad cuntzToAlbert_e1 = 0 := by
  apply ext_h3
  · simp [adjointQuad, cuntzToAlbert_e1, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]

theorem adjointQuad_e2_zero : adjointQuad cuntzToAlbert_e2 = 0 := by
  apply ext_h3
  · simp [adjointQuad, cuntzToAlbert_e2, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e2, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e2, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e2, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  · simp [adjointQuad, cuntzToAlbert_e2, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  · simp [adjointQuad, cuntzToAlbert_e2, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]

theorem linearTrace_e1 : linearTrace cuntzToAlbert_e1 = (1 : ℝ) := by
  simp [linearTrace_diagonal, cuntzToAlbert_e1]

theorem linearTrace_e2 : linearTrace cuntzToAlbert_e2 = (1 : ℝ) := by
  simp [linearTrace_diagonal, cuntzToAlbert_e2]

theorem crossProduct_e1_e1 : crossProduct cuntzToAlbert_e1 cuntzToAlbert_e1 = 0 := by
  rw [crossProduct_self, adjointQuad_e1_zero, smul_zero]

theorem crossProduct_e2_e2 : crossProduct cuntzToAlbert_e2 cuntzToAlbert_e2 = 0 := by
  rw [crossProduct_self, adjointQuad_e2_zero, smul_zero]

theorem crossProduct_e1_e2 :
    crossProduct cuntzToAlbert_e1 cuntzToAlbert_e2 = cuntzToAlbert_e3 := by
  rw [crossProduct, adjointQuad_e1_zero, adjointQuad_e2_zero, sub_zero, sub_zero]
  apply ext_h3
  · simp [adjointQuad, cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_e3,
          ZornVectorMatrix.add_zero, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_e3,
          ZornVectorMatrix.add_zero, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_e3,
          ZornVectorMatrix.add_zero, ZornVectorMatrix.norm_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_e3,
          ZornVectorMatrix.add_zero, ZornVectorMatrix.conj_zero,
          ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_e3,
          ZornVectorMatrix.add_zero, ZornVectorMatrix.conj_zero,
          ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  · simp [adjointQuad, cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_e3,
          ZornVectorMatrix.add_zero, ZornVectorMatrix.conj_zero,
          ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]

theorem linearTrace_crossProduct_e1_e2 :
    linearTrace (crossProduct cuntzToAlbert_e1 cuntzToAlbert_e2) = (1 : ℝ) := by
  rw [crossProduct_e1_e2]
  simp [linearTrace_diagonal, cuntzToAlbert_e3]

theorem jordanProduct_e1_e1 :
    jordanProduct cuntzToAlbert_e1 cuntzToAlbert_e1 = cuntzToAlbert_e1 := by
  change candidateJordanMul cuntzToAlbert_e1 cuntzToAlbert_e1 = cuntzToAlbert_e1
  rw [candidateJordanMul_trace_formula, linearTrace_e1, crossProduct_e1_e1]
  apply ext_h3 <;>
    (simp [cuntzToAlbert_e1, linearTrace, H3Zorn.one_readback, H3Zorn.sub_readback,
           ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero,
           ZornVectorMatrix.sub_self]; try ring)

theorem jordanProduct_e2_e2 :
    jordanProduct cuntzToAlbert_e2 cuntzToAlbert_e2 = cuntzToAlbert_e2 := by
  change candidateJordanMul cuntzToAlbert_e2 cuntzToAlbert_e2 = cuntzToAlbert_e2
  rw [candidateJordanMul_trace_formula, linearTrace_e2, crossProduct_e2_e2]
  apply ext_h3 <;>
    (simp [cuntzToAlbert_e2, linearTrace, H3Zorn.one_readback, H3Zorn.sub_readback,
           ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero,
           ZornVectorMatrix.sub_self]; try ring)

theorem jordanProduct_e1_e2 :
    jordanProduct cuntzToAlbert_e1 cuntzToAlbert_e2 = 0 := by
  change candidateJordanMul cuntzToAlbert_e1 cuntzToAlbert_e2 = 0
  rw [candidateJordanMul_trace_formula, linearTrace_e1, linearTrace_e2,
      linearTrace_crossProduct_e1_e2, crossProduct_e1_e2]
  apply ext_h3 <;>
    (simp [cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_e3,
           H3Zorn.one_readback, H3Zorn.sub_readback,
           ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero,
           ZornVectorMatrix.sub_self]; try ring)

theorem normCubic_spin_factor_vanishes (α β γ : ℝ) :
    normCubic (α • cuntzToAlbert_e1 + β • cuntzToAlbert_e2 + γ • cuntzToAlbert_Q1) = 0 := by
  simp [normCubic, cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_Q1,
        ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add,
        ZornVectorMatrix.norm_zero, ZornVectorMatrix.mul_zero, ZornVectorMatrix.trace_zero]

theorem cuntz_dual_seed_pair_embeds_as_spin_factor :
    jordanProduct cuntzToAlbert_e1 cuntzToAlbert_e1 = cuntzToAlbert_e1 ∧
    jordanProduct cuntzToAlbert_e2 cuntzToAlbert_e2 = cuntzToAlbert_e2 ∧
    jordanProduct cuntzToAlbert_e1 cuntzToAlbert_e2 = 0 ∧
    (∀ (α β γ : ℝ), normCubic (α • cuntzToAlbert_e1 + β • cuntzToAlbert_e2 + γ • cuntzToAlbert_Q1) = 0) ∧
    (Nonempty (CubicJordanDatum (H3Zorn ℝ))) := by
  refine ⟨jordanProduct_e1_e1, jordanProduct_e2_e2, jordanProduct_e1_e2,
          normCubic_spin_factor_vanishes, ⟨h3zornCubicJordanDatum⟩⟩

end InfoGeometry.Exceptional.DualSeedPairAlbertEmbedding
