import InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment
import InfoGeometry.Algebra.H3ZornCubicNormStructure
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.H3ZornCoordinateReadback
import InfoGeometry.Algebra.RealSplitOctSimp
import InfoGeometry.Exceptional.Freudenthal

/-! Freudenthal transport for the real split-Albert carrier.  The cubic data
are transported from the existing `H3Zorn` owner; no second determinant or
Jordan product is introduced here. -/

noncomputable section

set_option maxHeartbeats 1200000

namespace InfoGeometry.Algebra.RealAlbertMatrix

open InfoGeometry.Algebra
open InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment
open InfoGeometry.Exceptional.Freudenthal

def normCubic (X : RealAlbertMatrix) : ℝ :=
  H3Zorn.normCubic (toH3 X)

def adjointQuad (X : RealAlbertMatrix) : RealAlbertMatrix :=
  fromH3 (H3Zorn.adjointQuad (toH3 X))

/-! The first scalar projection of the `a`-block is compatible with the
coordinate Albert product.  This is intentionally kept separate from the
full `a`-block theorem: the remaining vector projections still require their
own coordinate readback. -/
theorem toH3_mul_a_a (X Y : RealAlbertMatrix) :
    (toH3 (RealAlbertMatrix.mul X Y)).a.a =
      (candidateJordanMul (toH3 X) (toH3 Y)).a.a := by
  change (RealSplitOctZornAlignment.toZorn
      (RealAlbertMatrix.mul X Y).z₃).a = _
  rw [_root_.rsm_mul_z3]
  rw [RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_mul,
    RealSplitOctZornAlignment.toZorn_conj_def,
    RealSplitOctZornAlignment.toZorn_mul,
    RealSplitOctZornAlignment.toZorn_conj_def]
  change _ = (candidateJordanMul (toH3 X) (toH3 Y)).a.a
  rw [candidateJordanMul_trace_formula]
  rw [H3Zorn.smul_readback, H3Zorn.sub_readback, H3Zorn.add_readback]
  dsimp
  rw [H3ZornCoordinateReadback.crossProduct_a, H3Zorn.smul_readback]
  rw [H3ZornCoordinateReadback.adjointQuad_a,
    H3ZornCoordinateReadback.adjointQuad_a,
    H3ZornCoordinateReadback.adjointQuad_a]
  rw [H3Zorn.add_readback]
  dsimp
  simp only [H3Zorn.add_readback]
  simp only [H3Zorn.linearTrace, H3Zorn.one_readback,
    H3Zorn.smul_readback, ZornVectorMatrix.zero,
    ZornVectorMatrix.smul_add, ZornVectorMatrix.add_smul,
    ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
    ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
    ← zvm_smul_def]
  simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
    ZornVectorMatrix.conj, ZornVectorMatrix.add,
    ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
    ZornVec3.cross, Fin.sum_univ_three, Finset.sum_add_distrib]
  simp [toH3]
  simp only [RealSplitOctZornAlignment.toZorn_conj_def]
  simp [ZornVectorMatrix.conj, RealSplitOctZornAlignment.toZorn]
  ring_nf

theorem toH3_mul_a (X Y : RealAlbertMatrix) :
    (toH3 (RealAlbertMatrix.mul X Y)).a =
      (candidateJordanMul (toH3 X) (toH3 Y)).a := by
  change RealSplitOctZornAlignment.toZorn
      (RealAlbertMatrix.mul X Y).z₃ = _
  rw [rsm_mul_z3]
  rw [RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_mul,
    RealSplitOctZornAlignment.toZorn_conj_def,
    RealSplitOctZornAlignment.toZorn_mul,
    RealSplitOctZornAlignment.toZorn_conj_def]
  change _ = (candidateJordanMul (toH3 X) (toH3 Y)).a
  rw [candidateJordanMul_trace_formula]
  rw [H3Zorn.smul_readback, H3Zorn.sub_readback, H3Zorn.add_readback]
  dsimp
  rw [H3ZornCoordinateReadback.crossProduct_a, H3Zorn.smul_readback]
  rw [H3ZornCoordinateReadback.adjointQuad_a,
    H3ZornCoordinateReadback.adjointQuad_a,
    H3ZornCoordinateReadback.adjointQuad_a]
  rw [H3Zorn.add_readback]
  dsimp
  simp only [H3Zorn.add_readback]
  simp only [H3Zorn.linearTrace, H3Zorn.one_readback,
    H3Zorn.smul_readback, ZornVectorMatrix.zero,
    ZornVectorMatrix.smul_add, ZornVectorMatrix.add_smul,
    ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
    ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
    ← zvm_smul_def]
  simp [toH3, RealSplitOctZornAlignment.toZorn,
    ZornVectorMatrix.conj]
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.conj, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three, Finset.sum_add_distrib,
      H3Zorn.add_readback, H3Zorn.smul_readback]
    ring
  · funext i
    fin_cases i <;>
      dsimp [ZornVectorMatrix.neg] <;>
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
        ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three,
        H3Zorn.add_readback, H3Zorn.smul_readback] <;>
      ring_nf <;>
      simp only [Finset.sum_add_distrib (s := Finset.univ),
        Finset.sum_neg_distrib] <;>
      ring
  · funext i
    fin_cases i <;>
      dsimp [ZornVectorMatrix.neg] <;>
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
        ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three,
        H3Zorn.add_readback, H3Zorn.smul_readback] <;>
      ring_nf <;>
      simp only [Finset.sum_add_distrib (s := Finset.univ),
        Finset.sum_neg_distrib] <;>
      ring
  · dsimp [ZornVectorMatrix.neg]
    simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.conj, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three, Finset.sum_add_distrib,
      H3Zorn.add_readback, H3Zorn.smul_readback]
    ring

theorem toH3_mul_b (X Y : RealAlbertMatrix) :
    (toH3 (RealAlbertMatrix.mul X Y)).b =
      (candidateJordanMul (toH3 X) (toH3 Y)).b := by
  change RealSplitOctZornAlignment.toZorn
      (RealAlbertMatrix.mul X Y).z₁ = _
  rw [rsm_mul_z1]
  rw [RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_mul,
    RealSplitOctZornAlignment.toZorn_conj_def,
    RealSplitOctZornAlignment.toZorn_mul,
    RealSplitOctZornAlignment.toZorn_conj_def]
  change _ = (candidateJordanMul (toH3 X) (toH3 Y)).b
  rw [candidateJordanMul_trace_formula]
  rw [H3Zorn.smul_readback, H3Zorn.sub_readback, H3Zorn.add_readback]
  dsimp
  rw [H3ZornCoordinateReadback.crossProduct_b, H3Zorn.smul_readback]
  rw [H3ZornCoordinateReadback.adjointQuad_b,
    H3ZornCoordinateReadback.adjointQuad_b,
    H3ZornCoordinateReadback.adjointQuad_b]
  rw [H3Zorn.add_readback]
  dsimp
  simp only [H3Zorn.add_readback]
  simp only [H3Zorn.linearTrace, H3Zorn.one_readback,
    H3Zorn.smul_readback, ZornVectorMatrix.zero,
    ZornVectorMatrix.smul_add, ZornVectorMatrix.add_smul,
    ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
    ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
    ← zvm_smul_def]
  simp [toH3, RealSplitOctZornAlignment.toZorn,
    ZornVectorMatrix.conj]
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.conj, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three, Finset.sum_add_distrib,
      H3Zorn.add_readback, H3Zorn.smul_readback] <;> ring
  · funext i
    fin_cases i <;>
      dsimp [ZornVectorMatrix.neg] <;>
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
        ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three,
        H3Zorn.add_readback, H3Zorn.smul_readback] <;>
      ring_nf <;>
      simp only [Finset.sum_add_distrib (s := Finset.univ),
        Finset.sum_neg_distrib] <;> ring
  · funext i
    fin_cases i <;>
      dsimp [ZornVectorMatrix.neg] <;>
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
        ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three,
        H3Zorn.add_readback, H3Zorn.smul_readback] <;>
      ring_nf <;>
      simp only [Finset.sum_add_distrib (s := Finset.univ),
        Finset.sum_neg_distrib] <;> ring
  · dsimp [ZornVectorMatrix.neg]
    simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.conj, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three, Finset.sum_add_distrib,
      H3Zorn.add_readback, H3Zorn.smul_readback] <;> ring

theorem toH3_mul_c (X Y : RealAlbertMatrix) :
    (toH3 (RealAlbertMatrix.mul X Y)).c =
      (candidateJordanMul (toH3 X) (toH3 Y)).c := by
  change RealSplitOctZornAlignment.toZorn
      (RealAlbertMatrix.mul X Y).z₂ = _
  rw [rsm_mul_z2]
  rw [RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_add,
    RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_smul_def,
    RealSplitOctZornAlignment.toZorn_mul,
    RealSplitOctZornAlignment.toZorn_conj_def,
    RealSplitOctZornAlignment.toZorn_mul,
    RealSplitOctZornAlignment.toZorn_conj_def]
  change _ = (candidateJordanMul (toH3 X) (toH3 Y)).c
  rw [candidateJordanMul_trace_formula]
  rw [H3Zorn.smul_readback, H3Zorn.sub_readback, H3Zorn.add_readback]
  dsimp
  rw [H3ZornCoordinateReadback.crossProduct_c, H3Zorn.smul_readback]
  rw [H3ZornCoordinateReadback.adjointQuad_c,
    H3ZornCoordinateReadback.adjointQuad_c,
    H3ZornCoordinateReadback.adjointQuad_c]
  rw [H3Zorn.add_readback]
  dsimp
  simp only [H3Zorn.add_readback]
  simp only [H3Zorn.linearTrace, H3Zorn.one_readback,
    H3Zorn.smul_readback, ZornVectorMatrix.zero,
    ZornVectorMatrix.smul_add, ZornVectorMatrix.add_smul,
    ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
    ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
    ← zvm_smul_def]
  simp [toH3, RealSplitOctZornAlignment.toZorn,
    ZornVectorMatrix.conj]
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.conj, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three, Finset.sum_add_distrib,
      H3Zorn.add_readback, H3Zorn.smul_readback]
    ring
  · funext i
    fin_cases i <;>
      dsimp [ZornVectorMatrix.neg] <;>
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
        ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three,
        H3Zorn.add_readback, H3Zorn.smul_readback] <;>
      ring_nf <;>
      simp only [Finset.sum_add_distrib (s := Finset.univ),
        Finset.sum_neg_distrib] <;>
      ring
  · funext i
    fin_cases i <;>
      dsimp [ZornVectorMatrix.neg] <;>
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
        ZornVectorMatrix.conj, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three,
        H3Zorn.add_readback, H3Zorn.smul_readback] <;>
      ring_nf <;>
      simp only [Finset.sum_add_distrib (s := Finset.univ),
        Finset.sum_neg_distrib] <;>
      ring
  · dsimp [ZornVectorMatrix.neg]
    simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero,
      ZornVectorMatrix.conj, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three, Finset.sum_add_distrib,
      H3Zorn.add_readback, H3Zorn.smul_readback]
    ring

theorem toH3_mul_α₁ (X Y : RealAlbertMatrix) :
    (toH3 (RealAlbertMatrix.mul X Y)).α₁ =
      (candidateJordanMul (toH3 X) (toH3 Y)).α₁ := by
  change (RealAlbertMatrix.mul X Y).α₁ = _
  rw [rsm_mul_a1]
  rw [candidateJordanMul_trace_formula]
  rw [H3Zorn.linearTrace_crossProduct]
  rw [H3Zorn.smul_readback, H3Zorn.sub_readback, H3Zorn.add_readback]
  dsimp
  rw [H3ZornCoordinateReadback.crossProduct_α₁,
    H3ZornCoordinateReadback.adjointQuad_α₁,
    H3ZornCoordinateReadback.adjointQuad_α₁,
    H3ZornCoordinateReadback.adjointQuad_α₁]
  simp only [H3ZornCoordinateReadback.linearTrace_coordinate,
    H3ZornCoordinateReadback.traceBilin_coordinate,
    H3ZornCoordinateReadback.crossProduct_α₁,
    H3ZornCoordinateReadback.adjointQuad_α₁,
    H3ZornCoordinateReadback.add_α₁,
    H3ZornCoordinateReadback.add_α₂,
    H3ZornCoordinateReadback.add_α₃,
    H3ZornCoordinateReadback.smul_α₁,
    H3ZornCoordinateReadback.smul_α₂,
    H3ZornCoordinateReadback.smul_α₃,
    H3Zorn.add_readback, H3Zorn.smul_readback, H3Zorn.one_readback]
  simp [toH3, RealSplitOctZornAlignment.toZorn,
    ZornVectorMatrix.norm, ZornVectorMatrix.trace,
    ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.add, ZornVectorMatrix.smul,
    ZornVectorMatrix.zero, ZornVectorMatrix.neg, ZornVec3.dot,
    Fin.sum_univ_three]
  ring_nf

theorem normCubic_smul (r : ℝ) (X : RealAlbertMatrix) :
    normCubic (RealAlbertMatrix.smul r X) = r ^ 3 * normCubic X := by
  change H3Zorn.normCubic (toH3 (RealAlbertMatrix.smul r X)) =
    r ^ 3 * H3Zorn.normCubic (toH3 X)
  rw [toH3_smul, H3Zorn.normCubic_smul]

theorem toH3_mul_α₂ (X Y : RealAlbertMatrix) :
    (toH3 (RealAlbertMatrix.mul X Y)).α₂ =
      (candidateJordanMul (toH3 X) (toH3 Y)).α₂ := by
  change (RealAlbertMatrix.mul X Y).α₂ = _
  rw [rsm_mul_a2, candidateJordanMul_trace_formula]
  rw [H3Zorn.linearTrace_crossProduct]
  rw [H3Zorn.smul_readback, H3Zorn.sub_readback, H3Zorn.add_readback]
  dsimp
  rw [H3ZornCoordinateReadback.crossProduct_α₂,
    H3ZornCoordinateReadback.adjointQuad_α₂,
    H3ZornCoordinateReadback.adjointQuad_α₂,
    H3ZornCoordinateReadback.adjointQuad_α₂]
  simp only [H3ZornCoordinateReadback.linearTrace_coordinate,
    H3ZornCoordinateReadback.traceBilin_coordinate,
    H3ZornCoordinateReadback.crossProduct_α₂,
    H3ZornCoordinateReadback.adjointQuad_α₂,
    H3ZornCoordinateReadback.add_α₁,
    H3ZornCoordinateReadback.add_α₂,
    H3ZornCoordinateReadback.add_α₃,
    H3ZornCoordinateReadback.smul_α₁,
    H3ZornCoordinateReadback.smul_α₂,
    H3ZornCoordinateReadback.smul_α₃,
    H3Zorn.add_readback, H3Zorn.smul_readback, H3Zorn.one_readback]
  simp [toH3, RealSplitOctZornAlignment.toZorn,
    ZornVectorMatrix.norm, ZornVectorMatrix.trace,
    ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.add, ZornVectorMatrix.smul,
    ZornVectorMatrix.zero, ZornVectorMatrix.neg, ZornVec3.dot,
    Fin.sum_univ_three]
  ring

theorem toH3_mul_α₃ (X Y : RealAlbertMatrix) :
    (toH3 (RealAlbertMatrix.mul X Y)).α₃ =
      (candidateJordanMul (toH3 X) (toH3 Y)).α₃ := by
  change (RealAlbertMatrix.mul X Y).α₃ = _
  rw [rsm_mul_a3, candidateJordanMul_trace_formula]
  rw [H3Zorn.linearTrace_crossProduct]
  rw [H3Zorn.smul_readback, H3Zorn.sub_readback, H3Zorn.add_readback]
  dsimp
  rw [H3ZornCoordinateReadback.crossProduct_α₃,
    H3ZornCoordinateReadback.adjointQuad_α₃,
    H3ZornCoordinateReadback.adjointQuad_α₃,
    H3ZornCoordinateReadback.adjointQuad_α₃]
  simp only [H3ZornCoordinateReadback.linearTrace_coordinate,
    H3ZornCoordinateReadback.traceBilin_coordinate,
    H3ZornCoordinateReadback.crossProduct_α₃,
    H3ZornCoordinateReadback.adjointQuad_α₃,
    H3ZornCoordinateReadback.add_α₁,
    H3ZornCoordinateReadback.add_α₂,
    H3ZornCoordinateReadback.add_α₃,
    H3ZornCoordinateReadback.smul_α₁,
    H3ZornCoordinateReadback.smul_α₂,
    H3ZornCoordinateReadback.smul_α₃,
    H3Zorn.add_readback, H3Zorn.smul_readback, H3Zorn.one_readback]
  simp [toH3, RealSplitOctZornAlignment.toZorn,
    ZornVectorMatrix.norm, ZornVectorMatrix.trace,
    ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.add, ZornVectorMatrix.smul,
    ZornVectorMatrix.zero, ZornVectorMatrix.neg, ZornVec3.dot,
    Fin.sum_univ_three]
  ring

theorem toH3_mul (X Y : RealAlbertMatrix) :
    toH3 (RealAlbertMatrix.mul X Y) =
      candidateJordanMul (toH3 X) (toH3 Y) := by
  apply H3Zorn.ext_h3
  · exact toH3_mul_α₁ X Y
  · exact toH3_mul_α₂ X Y
  · exact toH3_mul_α₃ X Y
  · exact toH3_mul_a X Y
  · exact toH3_mul_b X Y
  · exact toH3_mul_c X Y

noncomputable def toH3Linear : RealAlbertMatrix →ₗ[ℝ] H3Zorn ℝ where
  toFun := toH3
  map_add' := toH3_add
  map_smul' := toH3_smul

noncomputable def traceBilinLinear :
    RealAlbertMatrix →ₗ[ℝ] RealAlbertMatrix →ₗ[ℝ] ℝ where
  toFun X :=
    { toFun := fun Y =>
        h3zornTraceBilin (toH3 X) (toH3 Y)
      map_add' := by
        intro Y Z
        simpa only [toH3_add] using H3Zorn.traceBilin_add_right
          (toH3 X) (toH3 Y) (toH3 Z)
      map_smul' := by
        intro r Y
        simpa only [toH3_smul] using H3Zorn.traceBilin_smul_right
          r (toH3 X) (toH3 Y) }
  map_add' := by
    intro X Y
    ext Z
    simpa only [toH3_add] using H3Zorn.traceBilin_add_left
      (toH3 X) (toH3 Y) (toH3 Z)
  map_smul' := by
    intro r X
    ext Y
    simpa only [toH3_smul] using H3Zorn.traceBilin_smul_left
      r (toH3 X) (toH3 Y)

theorem freudenthal_identity_full (X : RealAlbertMatrix) :
    adjointQuad (adjointQuad X) = normCubic X • X := by
  have hto (Y : H3Zorn ℝ) : toH3 (fromH3 Y) = Y := by
    simpa [equiv, toH3, fromH3] using equiv.right_inv Y
  apply equiv.injective
  change toH3 (fromH3 (H3Zorn.adjointQuad (H3Zorn.adjointQuad (toH3 X)))) =
    toH3 (fromH3 (H3Zorn.normCubic (toH3 X) • toH3 X))
  rw [hto, hto]
  exact H3Zorn.adjointQuad_adjointQuad (toH3 X)

end InfoGeometry.Algebra.RealAlbertMatrix
