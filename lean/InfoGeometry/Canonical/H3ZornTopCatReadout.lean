import InfoGeometry.Algebra.H3ZornTopologicalReadout
import Mathlib.Topology.Category.TopCat.Basic

/-!
# `TopCat` readout for the native H₃(Zorn) operators

This file packages the continuity theorems proved by the H₃(Zorn) topology
owner as genuine morphisms in `TopCat`.  It introduces no new topology and
does not duplicate any algebraic operation.
-/

noncomputable section

namespace InfoGeometry.Algebra

open CategoryTheory

def h3ZornAlpha1ContinuousMap : ContinuousMap (H3Zorn ℝ) ℝ :=
  ContinuousMap.mk (fun X : H3Zorn ℝ => X.α₁) continuous_h3Zorn_α₁

def h3ZornAlpha2ContinuousMap : ContinuousMap (H3Zorn ℝ) ℝ :=
  ContinuousMap.mk (fun X : H3Zorn ℝ => X.α₂) continuous_h3Zorn_α₂

def h3ZornAlpha3ContinuousMap : ContinuousMap (H3Zorn ℝ) ℝ :=
  ContinuousMap.mk (fun X : H3Zorn ℝ => X.α₃) continuous_h3Zorn_α₃

def h3ZornAContinuousMap :
    ContinuousMap (H3Zorn ℝ) (ZornVectorMatrix ℝ) :=
  ContinuousMap.mk (fun X : H3Zorn ℝ => X.a) continuous_h3Zorn_a

def h3ZornBContinuousMap :
    ContinuousMap (H3Zorn ℝ) (ZornVectorMatrix ℝ) :=
  ContinuousMap.mk (fun X : H3Zorn ℝ => X.b) continuous_h3Zorn_b

def h3ZornCContinuousMap :
    ContinuousMap (H3Zorn ℝ) (ZornVectorMatrix ℝ) :=
  ContinuousMap.mk (fun X : H3Zorn ℝ => X.c) continuous_h3Zorn_c

def h3ZornAlpha1TopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : H3Zorn ℝ => X.α₁
      continuous_toFun := continuous_h3Zorn_α₁ }

def h3ZornAlpha2TopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : H3Zorn ℝ => X.α₂
      continuous_toFun := continuous_h3Zorn_α₂ }

def h3ZornAlpha3TopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : H3Zorn ℝ => X.α₃
      continuous_toFun := continuous_h3Zorn_α₃ }

def h3ZornATopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (ZornVectorMatrix ℝ) :=
  TopCat.ofHom
    { toFun := fun X : H3Zorn ℝ => X.a
      continuous_toFun := continuous_h3Zorn_a }

def h3ZornBTopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (ZornVectorMatrix ℝ) :=
  TopCat.ofHom
    { toFun := fun X : H3Zorn ℝ => X.b
      continuous_toFun := continuous_h3Zorn_b }

def h3ZornCTopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (ZornVectorMatrix ℝ) :=
  TopCat.ofHom
    { toFun := fun X : H3Zorn ℝ => X.c
      continuous_toFun := continuous_h3Zorn_c }

@[simp] theorem h3ZornAlpha1TopCat_apply (X : H3Zorn ℝ) :
    h3ZornAlpha1TopCat X = X.α₁ := rfl

@[simp] theorem h3ZornAlpha2TopCat_apply (X : H3Zorn ℝ) :
    h3ZornAlpha2TopCat X = X.α₂ := rfl

@[simp] theorem h3ZornAlpha3TopCat_apply (X : H3Zorn ℝ) :
    h3ZornAlpha3TopCat X = X.α₃ := rfl

@[simp] theorem h3ZornATopCat_apply (X : H3Zorn ℝ) :
    h3ZornATopCat X = X.a := rfl

@[simp] theorem h3ZornBTopCat_apply (X : H3Zorn ℝ) :
    h3ZornBTopCat X = X.b := rfl

@[simp] theorem h3ZornCTopCat_apply (X : H3Zorn ℝ) :
    h3ZornCTopCat X = X.c := rfl

def h3ZornNormCubicTopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := H3Zorn.normCubic
      continuous_toFun := continuous_h3Zorn_normCubic }

@[simp] theorem h3ZornNormCubicTopCat_apply (X : H3Zorn ℝ) :
    h3ZornNormCubicTopCat X = H3Zorn.normCubic X :=
  rfl

def h3ZornAdjointQuadTopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := H3Zorn.adjointQuad
      continuous_toFun := continuous_h3Zorn_adjointQuad }

@[simp] theorem h3ZornAdjointQuadTopCat_apply (X : H3Zorn ℝ) :
    h3ZornAdjointQuadTopCat X = H3Zorn.adjointQuad X :=
  rfl

def h3ZornJordanMulTopCat :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun p : H3Zorn ℝ × H3Zorn ℝ => p.1 * p.2
      continuous_toFun := continuous_h3Zorn_jordanMul }

@[simp] theorem h3ZornJordanMulTopCat_apply
    (p : H3Zorn ℝ × H3Zorn ℝ) :
    h3ZornJordanMulTopCat p = p.1 * p.2 :=
  rfl

def h3ZornPairSwapTopCat :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶
      TopCat.of (H3Zorn ℝ × H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := Prod.swap
      continuous_toFun := continuous_swap }

@[simp] theorem h3ZornPairSwapTopCat_apply
    (p : H3Zorn ℝ × H3Zorn ℝ) :
    h3ZornPairSwapTopCat p = (p.2, p.1) :=
  rfl

theorem h3ZornJordanMulTopCat_swap :
    h3ZornPairSwapTopCat ≫ h3ZornJordanMulTopCat =
      h3ZornJordanMulTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  exact candidateJordanMul_comm p.2 p.1

def h3ZornTraceBilinTopCat :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p : H3Zorn ℝ × H3Zorn ℝ => H3Zorn.traceBilin p.1 p.2
      continuous_toFun := continuous_h3Zorn_traceBilin }

@[simp] theorem h3ZornTraceBilinTopCat_apply
    (p : H3Zorn ℝ × H3Zorn ℝ) :
    h3ZornTraceBilinTopCat p = H3Zorn.traceBilin p.1 p.2 :=
  rfl

theorem h3ZornTraceBilinTopCat_swap :
    h3ZornPairSwapTopCat ≫ h3ZornTraceBilinTopCat =
      h3ZornTraceBilinTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  exact H3Zorn.traceBilin_symm p.2 p.1

def h3ZornCrossProductTopCat :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun p : H3Zorn ℝ × H3Zorn ℝ => H3Zorn.crossProduct p.1 p.2
      continuous_toFun := continuous_h3Zorn_crossProduct }

@[simp] theorem h3ZornCrossProductTopCat_apply
    (p : H3Zorn ℝ × H3Zorn ℝ) :
    h3ZornCrossProductTopCat p = H3Zorn.crossProduct p.1 p.2 :=
  rfl

theorem h3ZornCrossProductTopCat_swap :
    h3ZornPairSwapTopCat ≫ h3ZornCrossProductTopCat =
      h3ZornCrossProductTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  exact H3Zorn.crossProduct_symm p.2 p.1

def h3ZornUTopCat :
    TopCat.of (H3Zorn ℝ × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun p : H3Zorn ℝ × H3Zorn ℝ => H3Zorn.U p.1 p.2
      continuous_toFun := continuous_h3Zorn_U }

@[simp] theorem h3ZornUTopCat_apply
    (p : H3Zorn ℝ × H3Zorn ℝ) :
    h3ZornUTopCat p = H3Zorn.U p.1 p.2 :=
  rfl

def h3ZornTTopCat :
    TopCat.of ((H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ =>
        H3Zorn.T p.1.1 p.1.2 p.2
      continuous_toFun := continuous_h3Zorn_T }

@[simp] theorem h3ZornTTopCat_apply
    (p : (H3Zorn ℝ × H3Zorn ℝ) × H3Zorn ℝ) :
    h3ZornTTopCat p = H3Zorn.T p.1.1 p.1.2 p.2 :=
  rfl

def s3OnH3ZornReadoutTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := S3OnH3Zorn σ
      continuous_toFun := continuous_S3OnH3Zorn σ }

@[simp] theorem s3OnH3ZornReadoutTopCat_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    s3OnH3ZornReadoutTopCat σ X = S3OnH3Zorn σ X :=
  rfl

def normCubicAfterS3TopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : H3Zorn ℝ => H3Zorn.normCubic (S3OnH3Zorn σ X)
      continuous_toFun := continuous_h3Zorn_normCubic.comp
        (continuous_S3OnH3Zorn σ) }

@[simp] theorem normCubicAfterS3TopCat_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    normCubicAfterS3TopCat σ X =
      H3Zorn.normCubic (S3OnH3Zorn σ X) := by
  rfl

end InfoGeometry.Algebra
