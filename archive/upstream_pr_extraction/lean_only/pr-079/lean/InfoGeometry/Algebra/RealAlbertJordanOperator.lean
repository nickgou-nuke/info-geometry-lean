import Mathlib.Tactic
import InfoGeometry.Algebra.RealAlbertJordanProofs
import InfoGeometry.Algebra.RealSplitOctSimp

/-!
# Operator packaging for the split-Albert Jordan product

This owner packages the already defined coordinate product on
`RealAlbertMatrix` as a bilinear left-multiplication operator.  It records
only additivity and real-linearity; no associative or full Jordan-algebra
instance is introduced here.
-/

namespace InfoGeometry.Algebra

open RealSplitOct
open RealAlbertMatrix

noncomputable section

@[simp] theorem real_albert_add_α₁ (X Y : RealAlbertMatrix) :
    (X + Y).α₁ = X.α₁ + Y.α₁ := rfl
@[simp] theorem real_albert_add_α₂ (X Y : RealAlbertMatrix) :
    (X + Y).α₂ = X.α₂ + Y.α₂ := rfl
@[simp] theorem real_albert_add_α₃ (X Y : RealAlbertMatrix) :
    (X + Y).α₃ = X.α₃ + Y.α₃ := rfl
@[simp] theorem real_albert_add_z₁ (X Y : RealAlbertMatrix) :
    (X + Y).z₁ = X.z₁ + Y.z₁ := rfl
@[simp] theorem real_albert_add_z₂ (X Y : RealAlbertMatrix) :
    (X + Y).z₂ = X.z₂ + Y.z₂ := rfl
@[simp] theorem real_albert_add_z₃ (X Y : RealAlbertMatrix) :
    (X + Y).z₃ = X.z₃ + Y.z₃ := rfl

@[simp] theorem real_albert_smul_α₁ (r : ℝ) (X : RealAlbertMatrix) :
    (r • X).α₁ = r * X.α₁ := rfl
@[simp] theorem real_albert_smul_α₂ (r : ℝ) (X : RealAlbertMatrix) :
    (r • X).α₂ = r * X.α₂ := rfl
@[simp] theorem real_albert_smul_α₃ (r : ℝ) (X : RealAlbertMatrix) :
    (r • X).α₃ = r * X.α₃ := rfl
@[simp] theorem real_albert_smul_z₁ (r : ℝ) (X : RealAlbertMatrix) :
    (r • X).z₁ = r • X.z₁ := rfl
@[simp] theorem real_albert_smul_z₂ (r : ℝ) (X : RealAlbertMatrix) :
    (r • X).z₂ = r • X.z₂ := rfl
@[simp] theorem real_albert_smul_z₃ (r : ℝ) (X : RealAlbertMatrix) :
    (r • X).z₃ = r • X.z₃ := rfl

theorem real_split_oct_conj_add (X Y : RealSplitOct) :
    RealSplitOct.conj (X + Y) =
      RealSplitOct.conj X + RealSplitOct.conj Y := by
  ext <;> simp [RealSplitOct.conj, RealSplitOct.add] <;> ring

theorem real_split_oct_conj_smul (r : ℝ) (X : RealSplitOct) :
    RealSplitOct.conj (r • X) =
      r • RealSplitOct.conj X := by
  ext <;> simp [RealSplitOct.conj, RealSplitOct.smul] <;> ring

theorem real_split_oct_mul_add_left (X Y Z : RealSplitOct) :
    RealSplitOct.mul X (Y + Z) =
      RealSplitOct.mul X Y + RealSplitOct.mul X Z := by
  ext <;>
    simp only [RealSplitOct.mul_a, RealSplitOct.mul_b,
      RealSplitOct.mul_x0, RealSplitOct.mul_x1, RealSplitOct.mul_x2,
      RealSplitOct.mul_y0, RealSplitOct.mul_y1, RealSplitOct.mul_y2,
      RealSplitOct.add_a, RealSplitOct.add_b, RealSplitOct.add_x0,
      RealSplitOct.add_x1, RealSplitOct.add_x2, RealSplitOct.add_y0,
      RealSplitOct.add_y1, RealSplitOct.add_y2] <;>
    ring

theorem real_split_oct_mul_add_right (X Y Z : RealSplitOct) :
    RealSplitOct.mul (X + Y) Z =
      RealSplitOct.mul X Z + RealSplitOct.mul Y Z := by
  ext <;>
    simp only [RealSplitOct.mul_a, RealSplitOct.mul_b,
      RealSplitOct.mul_x0, RealSplitOct.mul_x1, RealSplitOct.mul_x2,
      RealSplitOct.mul_y0, RealSplitOct.mul_y1, RealSplitOct.mul_y2,
      RealSplitOct.add_a, RealSplitOct.add_b, RealSplitOct.add_x0,
      RealSplitOct.add_x1, RealSplitOct.add_x2, RealSplitOct.add_y0,
      RealSplitOct.add_y1, RealSplitOct.add_y2] <;>
    ring

theorem real_split_oct_mul_smul_left (r : ℝ) (X Y : RealSplitOct) :
    RealSplitOct.mul X (r • Y) = r • RealSplitOct.mul X Y := by
  ext <;>
    simp only [RealSplitOct.mul_a, RealSplitOct.mul_b,
      RealSplitOct.mul_x0, RealSplitOct.mul_x1, RealSplitOct.mul_x2,
      RealSplitOct.mul_y0, RealSplitOct.mul_y1, RealSplitOct.mul_y2,
      RealSplitOct.smul_a_tc, RealSplitOct.smul_b_tc,
      RealSplitOct.smul_x0_tc, RealSplitOct.smul_x1_tc,
      RealSplitOct.smul_x2_tc, RealSplitOct.smul_y0_tc,
      RealSplitOct.smul_y1_tc, RealSplitOct.smul_y2_tc] <;>
    ring

theorem real_split_oct_mul_smul_right (r : ℝ) (X Y : RealSplitOct) :
    RealSplitOct.mul (r • X) Y = r • RealSplitOct.mul X Y := by
  ext <;>
    simp only [RealSplitOct.mul_a, RealSplitOct.mul_b,
      RealSplitOct.mul_x0, RealSplitOct.mul_x1, RealSplitOct.mul_x2,
      RealSplitOct.mul_y0, RealSplitOct.mul_y1, RealSplitOct.mul_y2,
      RealSplitOct.smul_a_tc, RealSplitOct.smul_b_tc,
      RealSplitOct.smul_x0_tc, RealSplitOct.smul_x1_tc,
      RealSplitOct.smul_x2_tc, RealSplitOct.smul_y0_tc,
      RealSplitOct.smul_y1_tc, RealSplitOct.smul_y2_tc] <;>
    ring

theorem real_albert_jordan_mul_add_left
    (X Y Z : RealAlbertMatrix) :
    RealAlbertMatrix.mul X (Y + Z) =
      RealAlbertMatrix.mul X Y + RealAlbertMatrix.mul X Z := by
  ext <;>
    simp only [rsm_mul_a1, rsm_mul_a2, rsm_mul_a3, rsm_mul_z1,
      rsm_mul_z2, rsm_mul_z3, real_albert_add_α₁,
      real_albert_add_α₂, real_albert_add_α₃, real_albert_add_z₁,
      real_albert_add_z₂, real_albert_add_z₃,
      RealSplitOct.add_a, RealSplitOct.add_b, RealSplitOct.add_x0,
      RealSplitOct.add_x1, RealSplitOct.add_x2, RealSplitOct.add_y0,
      RealSplitOct.add_y1, RealSplitOct.add_y2, real_split_oct_conj_add,
      RealSplitOct.smul_a, RealSplitOct.smul_b, RealSplitOct.smul_x0,
      RealSplitOct.smul_x1, RealSplitOct.smul_x2, RealSplitOct.smul_y0,
      RealSplitOct.smul_y1, RealSplitOct.smul_y2,
      real_split_oct_mul_add_left, real_split_oct_mul_add_right,
      add_mul, mul_add, smul_add] <;>
    ring

theorem real_albert_jordan_mul_add_right
    (X Y Z : RealAlbertMatrix) :
    RealAlbertMatrix.mul (X + Y) Z =
      RealAlbertMatrix.mul X Z + RealAlbertMatrix.mul Y Z := by
  ext <;>
    simp only [rsm_mul_a1, rsm_mul_a2, rsm_mul_a3, rsm_mul_z1,
      rsm_mul_z2, rsm_mul_z3, real_albert_add_α₁,
      real_albert_add_α₂, real_albert_add_α₃, real_albert_add_z₁,
      real_albert_add_z₂, real_albert_add_z₃,
      RealSplitOct.add_a, RealSplitOct.add_b, RealSplitOct.add_x0,
      RealSplitOct.add_x1, RealSplitOct.add_x2, RealSplitOct.add_y0,
      RealSplitOct.add_y1, RealSplitOct.add_y2, real_split_oct_conj_add,
      RealSplitOct.smul_a, RealSplitOct.smul_b, RealSplitOct.smul_x0,
      RealSplitOct.smul_x1, RealSplitOct.smul_x2, RealSplitOct.smul_y0,
      RealSplitOct.smul_y1, RealSplitOct.smul_y2,
      real_split_oct_mul_add_left, real_split_oct_mul_add_right,
      add_mul, mul_add, smul_add] <;>
    ring

theorem real_albert_jordan_mul_smul_left
    (r : ℝ) (X Y : RealAlbertMatrix) :
    RealAlbertMatrix.mul X (r • Y) =
      r • RealAlbertMatrix.mul X Y := by
  ext <;>
    simp only [rsm_mul_a1, rsm_mul_a2, rsm_mul_a3, rsm_mul_z1,
      rsm_mul_z2, rsm_mul_z3, real_albert_smul_α₁,
      real_albert_smul_α₂, real_albert_smul_α₃, real_albert_smul_z₁,
      real_albert_smul_z₂, real_albert_smul_z₃,
      RealSplitOct.smul_a, RealSplitOct.smul_b, RealSplitOct.smul_x0,
      RealSplitOct.smul_x1, RealSplitOct.smul_x2, RealSplitOct.smul_y0,
      RealSplitOct.smul_y1, RealSplitOct.smul_y2,
      RealSplitOct.add_a, RealSplitOct.add_b, RealSplitOct.add_x0,
      RealSplitOct.add_x1, RealSplitOct.add_x2, RealSplitOct.add_y0,
      RealSplitOct.add_y1, RealSplitOct.add_y2,
      RealSplitOct.smul_a_tc, RealSplitOct.smul_b_tc,
      RealSplitOct.smul_x0_tc, RealSplitOct.smul_x1_tc,
      RealSplitOct.smul_x2_tc, RealSplitOct.smul_y0_tc,
      RealSplitOct.smul_y1_tc, RealSplitOct.smul_y2_tc,
      real_split_oct_conj_smul, real_split_oct_mul_smul_left,
      real_split_oct_mul_smul_right, mul_smul_comm, smul_mul_assoc,
      smul_add, smul_smul] <;>
    ring

theorem real_albert_jordan_mul_smul_right
    (r : ℝ) (X Y : RealAlbertMatrix) :
    RealAlbertMatrix.mul (r • X) Y =
      r • RealAlbertMatrix.mul X Y := by
  ext <;>
    simp only [rsm_mul_a1, rsm_mul_a2, rsm_mul_a3, rsm_mul_z1,
      rsm_mul_z2, rsm_mul_z3, real_albert_smul_α₁,
      real_albert_smul_α₂, real_albert_smul_α₃, real_albert_smul_z₁,
      real_albert_smul_z₂, real_albert_smul_z₃,
      RealSplitOct.smul_a, RealSplitOct.smul_b, RealSplitOct.smul_x0,
      RealSplitOct.smul_x1, RealSplitOct.smul_x2, RealSplitOct.smul_y0,
      RealSplitOct.smul_y1, RealSplitOct.smul_y2,
      RealSplitOct.add_a, RealSplitOct.add_b, RealSplitOct.add_x0,
      RealSplitOct.add_x1, RealSplitOct.add_x2, RealSplitOct.add_y0,
      RealSplitOct.add_y1, RealSplitOct.add_y2,
      RealSplitOct.smul_a_tc, RealSplitOct.smul_b_tc,
      RealSplitOct.smul_x0_tc, RealSplitOct.smul_x1_tc,
      RealSplitOct.smul_x2_tc, RealSplitOct.smul_y0_tc,
      RealSplitOct.smul_y1_tc, RealSplitOct.smul_y2_tc,
      real_split_oct_conj_smul, real_split_oct_mul_smul_left,
      real_split_oct_mul_smul_right, mul_smul_comm, smul_mul_assoc,
      smul_add, smul_smul] <;>
    ring

noncomputable def realAlbertJordanLeft
    (X : RealAlbertMatrix) : RealAlbertMatrix →ₗ[ℝ] RealAlbertMatrix where
  toFun Y := RealAlbertMatrix.mul X Y
  map_add' Y Z := real_albert_jordan_mul_add_left X Y Z
  map_smul' r Y := real_albert_jordan_mul_smul_left r X Y

@[simp] theorem realAlbertJordanLeft_apply
    (X Y : RealAlbertMatrix) :
    realAlbertJordanLeft X Y = RealAlbertMatrix.mul X Y := rfl

noncomputable def realAlbertJordanRight
    (X : RealAlbertMatrix) : RealAlbertMatrix →ₗ[ℝ] RealAlbertMatrix where
  toFun Y := RealAlbertMatrix.mul Y X
  map_add' Y Z := real_albert_jordan_mul_add_right Y Z X
  map_smul' r Y := real_albert_jordan_mul_smul_right r Y X

@[simp] theorem realAlbertJordanRight_apply
    (X Y : RealAlbertMatrix) :
    realAlbertJordanRight X Y = RealAlbertMatrix.mul Y X := rfl

theorem realAlbertJordanLeft_eq_right
    (X : RealAlbertMatrix) :
    realAlbertJordanLeft X = realAlbertJordanRight X := by
  apply LinearMap.ext
  intro Y
  change RealAlbertMatrix.mul X Y = RealAlbertMatrix.mul Y X
  exact real_albert_jordan_comm X Y

end
end InfoGeometry.Algebra
