import Mathlib
import proofs.SplitOctonionAlgebra
import proofs.SplitOctonionNorm44

set_option linter.unusedSimpArgs false
open SplitOctonion
open SplitOctonionNorm44
open Quaternion

def lmul (α : SplitOct) : SplitOct →ₗ[ℝ] SplitOct where
  toFun x := α * x
  map_add' x y := left_distrib α x y
  map_smul' c x := by exact (smul_comm c α x).symm

def rmul (α : SplitOct) : SplitOct →ₗ[ℝ] SplitOct where
  toFun x := x * α
  map_add' x y := right_distrib x y α
  map_smul' c x := smul_mul_assoc c x α

lemma splitBilinear_eq (x y : SplitOct) : splitBilinear x y = (x.a * star y.a - x.b * star y.b).re := by
  dsimp [splitBilinear, splitNorm, add_def, sub_def]
  simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
             Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
             Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
             Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

lemma quat_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring

def is_imaginary (α : SplitOct) : Prop := α.a.re = 0 ∧ α.b = 0

lemma lmul_skew_of_imaginary (α : SplitOct) (h : is_imaginary α) (x y : SplitOct) :
  splitBilinear (α * x) y + splitBilinear x (α * y) = 0 := by
  dsimp [is_imaginary] at h
  rcases h with ⟨h1, h2⟩
  have h_star_a : star α.a = -α.a := by
    ext
    · simp only [Quaternion.re_star, h1, neg_zero, Quaternion.re_neg]
    · simp only [Quaternion.imI_star, Quaternion.imI_neg]
    · simp only [Quaternion.imJ_star, Quaternion.imJ_neg]
    · simp only [Quaternion.imK_star, Quaternion.imK_neg]
  simp only [splitBilinear_eq, mul_def, h2, zero_mul, mul_zero, star_zero, sub_zero, add_zero, zero_add, sub_self]
  have H1 : ((α.a * x.a) * star y.a + x.a * star (α.a * y.a)).re = 0 := by
    calc ((α.a * x.a) * star y.a + x.a * star (α.a * y.a)).re
      _ = ((α.a * x.a) * star y.a).re + (x.a * star (α.a * y.a)).re := by rw [Quaternion.re_add]
      _ = (α.a * (x.a * star y.a)).re + (x.a * star (α.a * y.a)).re := by rw [mul_assoc]
      _ = (α.a * (x.a * star y.a)).re + (x.a * (star y.a * star α.a)).re := by rw [star_mul]
      _ = (α.a * (x.a * star y.a)).re + (x.a * (star y.a * -α.a)).re := by rw [h_star_a]
      _ = (α.a * (x.a * star y.a)).re + (x.a * -(star y.a * α.a)).re := by rw [mul_neg]
      _ = (α.a * (x.a * star y.a)).re + -(x.a * (star y.a * α.a)).re := by rw [mul_neg, Quaternion.re_neg]
      _ = (α.a * (x.a * star y.a)).re + -((x.a * star y.a) * α.a).re := by rw [mul_assoc]
      _ = ((x.a * star y.a) * α.a).re - ((x.a * star y.a) * α.a).re := by rw [quat_re_mul_comm α.a (x.a * star y.a), sub_eq_add_neg]
      _ = 0 := by ring
  have H2 : ((x.b * α.a) * star y.b + x.b * star (y.b * α.a)).re = 0 := by
    calc ((x.b * α.a) * star y.b + x.b * star (y.b * α.a)).re
      _ = ((x.b * α.a) * star y.b).re + (x.b * star (y.b * α.a)).re := by rw [Quaternion.re_add]
      _ = ((x.b * α.a) * star y.b).re + (x.b * (star α.a * star y.b)).re := by rw [star_mul]
      _ = ((x.b * α.a) * star y.b).re + (x.b * (-α.a * star y.b)).re := by rw [h_star_a]
      _ = ((x.b * α.a) * star y.b).re + (x.b * -(α.a * star y.b)).re := by rw [neg_mul]
      _ = ((x.b * α.a) * star y.b).re + -(x.b * (α.a * star y.b)).re := by rw [mul_neg, Quaternion.re_neg]
      _ = ((x.b * α.a) * star y.b).re + -((x.b * α.a) * star y.b).re := by rw [mul_assoc]
      _ = 0 := by ring
  calc ((α.a * x.a) * star y.a - (x.b * α.a) * star y.b).re + (x.a * star (α.a * y.a) - x.b * star (y.b * α.a)).re
    _ = ((α.a * x.a) * star y.a).re - ((x.b * α.a) * star y.b).re + ((x.a * star (α.a * y.a)).re - (x.b * star (y.b * α.a)).re) := by
      rw [Quaternion.re_sub, Quaternion.re_sub]
    _ = ((α.a * x.a) * star y.a).re + (x.a * star (α.a * y.a)).re - (((x.b * α.a) * star y.b).re + (x.b * star (y.b * α.a)).re) := by ring
    _ = 0 - 0 := by
      have h1_eq : ((α.a * x.a) * star y.a).re + (x.a * star (α.a * y.a)).re = 0 := by
        calc ((α.a * x.a) * star y.a).re + (x.a * star (α.a * y.a)).re
          _ = ((α.a * x.a) * star y.a + x.a * star (α.a * y.a)).re := by rw [Quaternion.re_add]
          _ = 0 := H1
      have h2_eq : ((x.b * α.a) * star y.b).re + (x.b * star (y.b * α.a)).re = 0 := by
        calc ((x.b * α.a) * star y.b).re + (x.b * star (y.b * α.a)).re
          _ = ((x.b * α.a) * star y.b + x.b * star (y.b * α.a)).re := by rw [Quaternion.re_add]
          _ = 0 := H2
      rw [h1_eq, h2_eq]
    _ = 0 := by ring

lemma rmul_skew_of_imaginary (α : SplitOct) (h : is_imaginary α) (x y : SplitOct) :
  splitBilinear (x * α) y + splitBilinear x (y * α) = 0 := by
  dsimp [is_imaginary] at h
  rcases h with ⟨h1, h2⟩
  have h_star_a : star α.a = -α.a := by
    ext
    · simp only [Quaternion.re_star, h1, neg_zero, Quaternion.re_neg]
    · simp only [Quaternion.imI_star, Quaternion.imI_neg]
    · simp only [Quaternion.imJ_star, Quaternion.imJ_neg]
    · simp only [Quaternion.imK_star, Quaternion.imK_neg]
  simp only [splitBilinear_eq, mul_def, h2, zero_mul, mul_zero, star_zero, sub_zero, add_zero, zero_add, sub_self]
  have H1 : ((x.a * α.a) * star y.a + x.a * star (y.a * α.a)).re = 0 := by
    calc ((x.a * α.a) * star y.a + x.a * star (y.a * α.a)).re
      _ = ((x.a * α.a) * star y.a).re + (x.a * star (y.a * α.a)).re := by rw [Quaternion.re_add]
      _ = ((x.a * α.a) * star y.a).re + (x.a * (star α.a * star y.a)).re := by rw [star_mul]
      _ = ((x.a * α.a) * star y.a).re + (x.a * (-α.a * star y.a)).re := by rw [h_star_a]
      _ = ((x.a * α.a) * star y.a).re + (x.a * -(α.a * star y.a)).re := by rw [neg_mul]
      _ = ((x.a * α.a) * star y.a).re + -(x.a * (α.a * star y.a)).re := by rw [mul_neg, Quaternion.re_neg]
      _ = ((x.a * α.a) * star y.a).re + -((x.a * α.a) * star y.a).re := by rw [mul_assoc]
      _ = 0 := by ring
  have H2 : ((x.b * star α.a) * star y.b + x.b * star (y.b * star α.a)).re = 0 := by
    calc ((x.b * star α.a) * star y.b + x.b * star (y.b * star α.a)).re
      _ = ((x.b * star α.a) * star y.b).re + (x.b * star (y.b * star α.a)).re := by rw [Quaternion.re_add]
      _ = ((x.b * -α.a) * star y.b).re + (x.b * star (y.b * -α.a)).re := by rw [h_star_a]
      _ = (-(x.b * α.a) * star y.b).re + (x.b * star (-(y.b * α.a))).re := by rw [mul_neg, mul_neg]
      _ = -(x.b * α.a * star y.b).re + (x.b * -(star (y.b * α.a))).re := by rw [neg_mul, Quaternion.re_neg, star_neg]
      _ = -((x.b * α.a) * star y.b).re + -(x.b * star (y.b * α.a)).re := by rw [mul_assoc, mul_neg, Quaternion.re_neg]
      _ = -((x.b * α.a) * star y.b).re + -(x.b * (star α.a * star y.b)).re := by rw [star_mul]
      _ = -((x.b * α.a) * star y.b).re + -(x.b * (-α.a * star y.b)).re := by rw [h_star_a]
      _ = -((x.b * α.a) * star y.b).re + -(x.b * -(α.a * star y.b)).re := by rw [neg_mul]
      _ = -((x.b * α.a) * star y.b).re + - -(x.b * (α.a * star y.b)).re := by rw [mul_neg, Quaternion.re_neg]
      _ = -((x.b * α.a) * star y.b).re + (x.b * α.a * star y.b).re := by rw [neg_neg, mul_assoc]
      _ = 0 := by ring
  calc ((x.a * α.a) * star y.a - (x.b * star α.a) * star y.b).re + (x.a * star (y.a * α.a) - x.b * star (y.b * star α.a)).re
    _ = ((x.a * α.a) * star y.a).re - ((x.b * star α.a) * star y.b).re + ((x.a * star (y.a * α.a)).re - (x.b * star (y.b * star α.a)).re) := by
      rw [Quaternion.re_sub, Quaternion.re_sub]
    _ = ((x.a * α.a) * star y.a).re + (x.a * star (y.a * α.a)).re - (((x.b * star α.a) * star y.b).re + (x.b * star (y.b * star α.a)).re) := by ring
    _ = 0 - 0 := by
      have h1_eq : ((x.a * α.a) * star y.a).re + (x.a * star (y.a * α.a)).re = 0 := by
        calc ((x.a * α.a) * star y.a).re + (x.a * star (y.a * α.a)).re
          _ = ((x.a * α.a) * star y.a + x.a * star (y.a * α.a)).re := by rw [Quaternion.re_add]
          _ = 0 := H1
      have h2_eq : ((x.b * star α.a) * star y.b).re + (x.b * star (y.b * star α.a)).re = 0 := by
        calc ((x.b * star α.a) * star y.b).re + (x.b * star (y.b * star α.a)).re
          _ = ((x.b * star α.a) * star y.b + x.b * star (y.b * star α.a)).re := by rw [Quaternion.re_add]
          _ = 0 := H2
      rw [h1_eq, h2_eq]
    _ = 0 := by ring
