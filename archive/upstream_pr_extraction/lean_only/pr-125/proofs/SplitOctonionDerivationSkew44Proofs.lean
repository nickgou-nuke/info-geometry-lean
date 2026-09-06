import proofs.SplitOctonionDerivationSpace
import proofs.SplitOctonionNorm44
import Mathlib.Tactic.Ring

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open SplitOctonion
open SplitOctonionNorm44
open OctDerivation

lemma bmul_0_0 : basis 0 * basis 0 = basis 0 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_0_1 : basis 0 * basis 1 = basis 1 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_0_2 : basis 0 * basis 2 = basis 2 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_0_3 : basis 0 * basis 3 = basis 3 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_0_4 : basis 0 * basis 4 = basis 4 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_0_5 : basis 0 * basis 5 = basis 5 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_0_6 : basis 0 * basis 6 = basis 6 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_0_7 : basis 0 * basis 7 = basis 7 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_1_0 : basis 1 * basis 0 = basis 1 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_1_1 : basis 1 * basis 1 = -basis 0 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_1_2 : basis 1 * basis 2 = basis 3 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_1_3 : basis 1 * basis 3 = -basis 2 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_1_4 : basis 1 * basis 4 = basis 5 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_1_5 : basis 1 * basis 5 = -basis 4 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_1_6 : basis 1 * basis 6 = -basis 7 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_1_7 : basis 1 * basis 7 = basis 6 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_2_0 : basis 2 * basis 0 = basis 2 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_2_1 : basis 2 * basis 1 = -basis 3 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_2_2 : basis 2 * basis 2 = -basis 0 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_2_3 : basis 2 * basis 3 = basis 1 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_2_4 : basis 2 * basis 4 = basis 6 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_2_5 : basis 2 * basis 5 = basis 7 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_2_6 : basis 2 * basis 6 = -basis 4 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_2_7 : basis 2 * basis 7 = -basis 5 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_3_0 : basis 3 * basis 0 = basis 3 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_3_1 : basis 3 * basis 1 = basis 2 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_3_2 : basis 3 * basis 2 = -basis 1 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_3_3 : basis 3 * basis 3 = -basis 0 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_3_4 : basis 3 * basis 4 = basis 7 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_3_5 : basis 3 * basis 5 = -basis 6 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_3_6 : basis 3 * basis 6 = basis 5 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_3_7 : basis 3 * basis 7 = -basis 4 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_4_0 : basis 4 * basis 0 = basis 4 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_4_1 : basis 4 * basis 1 = -basis 5 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_4_2 : basis 4 * basis 2 = -basis 6 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_4_3 : basis 4 * basis 3 = -basis 7 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_4_4 : basis 4 * basis 4 = basis 0 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_4_5 : basis 4 * basis 5 = -basis 1 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_4_6 : basis 4 * basis 6 = -basis 2 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_4_7 : basis 4 * basis 7 = -basis 3 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_5_0 : basis 5 * basis 0 = basis 5 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_5_1 : basis 5 * basis 1 = basis 4 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_5_2 : basis 5 * basis 2 = -basis 7 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_5_3 : basis 5 * basis 3 = basis 6 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_5_4 : basis 5 * basis 4 = basis 1 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_5_5 : basis 5 * basis 5 = basis 0 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_5_6 : basis 5 * basis 6 = basis 3 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_5_7 : basis 5 * basis 7 = -basis 2 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_6_0 : basis 6 * basis 0 = basis 6 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_6_1 : basis 6 * basis 1 = basis 7 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_6_2 : basis 6 * basis 2 = basis 4 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_6_3 : basis 6 * basis 3 = -basis 5 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_6_4 : basis 6 * basis 4 = basis 2 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_6_5 : basis 6 * basis 5 = -basis 3 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_6_6 : basis 6 * basis 6 = basis 0 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_6_7 : basis 6 * basis 7 = basis 1 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_7_0 : basis 7 * basis 0 = basis 7 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_7_1 : basis 7 * basis 1 = -basis 6 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_7_2 : basis 7 * basis 2 = basis 5 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_7_3 : basis 7 * basis 3 = basis 4 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_7_4 : basis 7 * basis 4 = basis 3 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_7_5 : basis 7 * basis 5 = basis 2 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_7_6 : basis 7 * basis 6 = -basis 1 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring
lemma bmul_7_7 : basis 7 * basis 7 = basis 0 := by ext1 <;> ext1 <;> simp [basis, mul_def, add_def, sub_def, smul_def, neg_def, star, zero_def, one_def] <;> ring

lemma skew_proof_0_0 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 0)) (basis 0) + splitBilinear (basis 0) (D.toLinearMap (basis 0)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 0)) (basis 0) + splitBilinear (basis 0) (D.toLinearMap (basis 0)) = (-2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 0) := by
    simp only [bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_0_1 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 0)) (basis 1) + splitBilinear (basis 0) (D.toLinearMap (basis 1)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 0)) (basis 1) + splitBilinear (basis 0) (D.toLinearMap (basis 1)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 1) := by
    simp only [bmul_1_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_0_2 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 0)) (basis 2) + splitBilinear (basis 0) (D.toLinearMap (basis 2)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 0)) (basis 2) + splitBilinear (basis 0) (D.toLinearMap (basis 2)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 1) := by
    simp only [bmul_1_2, bmul_2_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_2, bmul_2_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL12, hL21, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_0_3 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 0)) (basis 3) + splitBilinear (basis 0) (D.toLinearMap (basis 3)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 0)) (basis 3) + splitBilinear (basis 0) (D.toLinearMap (basis 3)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 0) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 0) := by
    simp only [bmul_1_2, bmul_2_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_2, bmul_2_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL12, hL21, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_0_4 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 0)) (basis 4) + splitBilinear (basis 0) (D.toLinearMap (basis 4)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 0)) (basis 4) + splitBilinear (basis 0) (D.toLinearMap (basis 4)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 4) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 7) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 3) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 3) := by
    simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL34, hL24, hL16, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_0_5 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 0)) (basis 5) + splitBilinear (basis 0) (D.toLinearMap (basis 5)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 0)) (basis 5) + splitBilinear (basis 0) (D.toLinearMap (basis 5)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 5) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 6) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 2) := by
    simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL34, hL24, hL16, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_0_6 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 0)) (basis 6) + splitBilinear (basis 0) (D.toLinearMap (basis 6)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 0)) (basis 6) + splitBilinear (basis 0) (D.toLinearMap (basis 6)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 6) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 5) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 0) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 1) := by
    simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL34, hL24, hL16, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_0_7 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 0)) (basis 7) + splitBilinear (basis 0) (D.toLinearMap (basis 7)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 0)) (basis 7) + splitBilinear (basis 0) (D.toLinearMap (basis 7)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 7) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 4) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL34, hL24, hL16, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_1_0 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 1)) (basis 0) + splitBilinear (basis 1) (D.toLinearMap (basis 0)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 1)) (basis 0) + splitBilinear (basis 1) (D.toLinearMap (basis 0)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 1) := by
    simp only [bmul_1_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_1_1 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 1)) (basis 1) + splitBilinear (basis 1) (D.toLinearMap (basis 1)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 1)) (basis 1) + splitBilinear (basis 1) (D.toLinearMap (basis 1)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 0) := by
    simp only [bmul_1_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_1_2 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 1)) (basis 2) + splitBilinear (basis 1) (D.toLinearMap (basis 2)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 1)) (basis 2) + splitBilinear (basis 1) (D.toLinearMap (basis 2)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 0) := by
    simp only [bmul_2_1, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_2_1, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL21, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_1_3 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 1)) (basis 3) + splitBilinear (basis 1) (D.toLinearMap (basis 3)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 1)) (basis 3) + splitBilinear (basis 1) (D.toLinearMap (basis 3)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 1) := by
    simp only [bmul_2_1, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_2_1, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL21, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_1_4 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 1)) (basis 4) + splitBilinear (basis 1) (D.toLinearMap (basis 4)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 1)) (basis 4) + splitBilinear (basis 1) (D.toLinearMap (basis 4)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 6) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 2) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 3) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 2) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_1_5 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 1)) (basis 5) + splitBilinear (basis 1) (D.toLinearMap (basis 5)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 1)) (basis 5) + splitBilinear (basis 1) (D.toLinearMap (basis 5)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 7) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 3) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 3) := by
    simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL34, hL24, hL16, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_1_6 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 1)) (basis 6) + splitBilinear (basis 1) (D.toLinearMap (basis 6)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 1)) (basis 6) + splitBilinear (basis 1) (D.toLinearMap (basis 6)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 4) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_1_7 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 1)) (basis 7) + splitBilinear (basis 1) (D.toLinearMap (basis 7)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 1)) (basis 7) + splitBilinear (basis 1) (D.toLinearMap (basis 7)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 5) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 1) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_2_0 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 2)) (basis 0) + splitBilinear (basis 2) (D.toLinearMap (basis 0)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 2)) (basis 0) + splitBilinear (basis 2) (D.toLinearMap (basis 0)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 1) := by
    simp only [bmul_1_2, bmul_2_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_2, bmul_2_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL12, hL21, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_2_1 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 2)) (basis 1) + splitBilinear (basis 2) (D.toLinearMap (basis 1)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 2)) (basis 1) + splitBilinear (basis 2) (D.toLinearMap (basis 1)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 0) := by
    simp only [bmul_2_1, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_2_1, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL21, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_2_2 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 2)) (basis 2) + splitBilinear (basis 2) (D.toLinearMap (basis 2)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 2)) (basis 2) + splitBilinear (basis 2) (D.toLinearMap (basis 2)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 2 * basis 2) - D.toLinearMap (basis 2) * basis 2 - basis 2 * D.toLinearMap (basis 2)) (basis 0) := by
    simp only [bmul_2_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL22 := hL (basis 2) (basis 2)
  rw [bmul_2_2] at hL22
  have map_neg_2_2 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_2_2] at hL22
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_2_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL22, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_2_3 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 2)) (basis 3) + splitBilinear (basis 2) (D.toLinearMap (basis 3)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 2)) (basis 3) + splitBilinear (basis 2) (D.toLinearMap (basis 3)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 1) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 2) := by
    simp only [bmul_1_1, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_2_4 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 2)) (basis 4) + splitBilinear (basis 2) (D.toLinearMap (basis 4)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 2)) (basis 4) + splitBilinear (basis 2) (D.toLinearMap (basis 4)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 5) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 1) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_2_5 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 2)) (basis 5) + splitBilinear (basis 2) (D.toLinearMap (basis 5)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 2)) (basis 5) + splitBilinear (basis 2) (D.toLinearMap (basis 5)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 4) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL34, hL24, hL16, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_2_6 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 2)) (basis 6) + splitBilinear (basis 2) (D.toLinearMap (basis 6)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 2)) (basis 6) + splitBilinear (basis 2) (D.toLinearMap (basis 6)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 7) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 3) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_2_7 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 2)) (basis 7) + splitBilinear (basis 2) (D.toLinearMap (basis 7)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 2)) (basis 7) + splitBilinear (basis 2) (D.toLinearMap (basis 7)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 6) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 2) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 2) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_3_0 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 3)) (basis 0) + splitBilinear (basis 3) (D.toLinearMap (basis 0)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 3)) (basis 0) + splitBilinear (basis 3) (D.toLinearMap (basis 0)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 0) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 0) := by
    simp only [bmul_1_2, bmul_2_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_2, bmul_2_1, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL12, hL21, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_3_1 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 3)) (basis 1) + splitBilinear (basis 3) (D.toLinearMap (basis 1)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 3)) (basis 1) + splitBilinear (basis 3) (D.toLinearMap (basis 1)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 1) := by
    simp only [bmul_2_1, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_2_1, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL21, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_3_2 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 3)) (basis 2) + splitBilinear (basis 3) (D.toLinearMap (basis 2)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 3)) (basis 2) + splitBilinear (basis 3) (D.toLinearMap (basis 2)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 1) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 2) := by
    simp only [bmul_1_1, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_3_3 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 3)) (basis 3) + splitBilinear (basis 3) (D.toLinearMap (basis 3)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 3)) (basis 3) + splitBilinear (basis 3) (D.toLinearMap (basis 3)) = (-2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 0) + (2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 3) + (1) * splitBilinear (D.toLinearMap (basis 2 * basis 2) - D.toLinearMap (basis 2) * basis 2 - basis 2 * D.toLinearMap (basis 2)) (basis 0) := by
    simp only [bmul_1_1, bmul_1_2, bmul_2_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL22 := hL (basis 2) (basis 2)
  rw [bmul_2_2] at hL22
  have map_neg_2_2 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_2_2] at hL22
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_1_2, bmul_2_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL12, hL22, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_3_4 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 3)) (basis 4) + splitBilinear (basis 3) (D.toLinearMap (basis 4)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 3)) (basis 4) + splitBilinear (basis 3) (D.toLinearMap (basis 4)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 4) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 0) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_3_5 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 3)) (basis 5) + splitBilinear (basis 3) (D.toLinearMap (basis 5)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 3)) (basis 5) + splitBilinear (basis 3) (D.toLinearMap (basis 5)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 5) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 1) := by
    simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL34, hL24, hL16, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_3_6 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 3)) (basis 6) + splitBilinear (basis 3) (D.toLinearMap (basis 6)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 3)) (basis 6) + splitBilinear (basis 3) (D.toLinearMap (basis 6)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 6) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 2) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 2) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_3_7 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 3)) (basis 7) + splitBilinear (basis 3) (D.toLinearMap (basis 7)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 3)) (basis 7) + splitBilinear (basis 3) (D.toLinearMap (basis 7)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 7) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 3) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 2) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 3) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_4_0 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 4)) (basis 0) + splitBilinear (basis 4) (D.toLinearMap (basis 0)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 4)) (basis 0) + splitBilinear (basis 4) (D.toLinearMap (basis 0)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 4) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 7) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 3) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 3) := by
    simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL34, hL24, hL16, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_4_1 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 4)) (basis 1) + splitBilinear (basis 4) (D.toLinearMap (basis 1)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 4)) (basis 1) + splitBilinear (basis 4) (D.toLinearMap (basis 1)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 6) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 2) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 3) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 2) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_4_2 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 4)) (basis 2) + splitBilinear (basis 4) (D.toLinearMap (basis 2)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 4)) (basis 2) + splitBilinear (basis 4) (D.toLinearMap (basis 2)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 5) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 1) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_4_3 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 4)) (basis 3) + splitBilinear (basis 4) (D.toLinearMap (basis 3)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 4)) (basis 3) + splitBilinear (basis 4) (D.toLinearMap (basis 3)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 4) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 0) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_4_4 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 4)) (basis 4) + splitBilinear (basis 4) (D.toLinearMap (basis 4)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 4)) (basis 4) + splitBilinear (basis 4) (D.toLinearMap (basis 4)) = (1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 4 * basis 4) - D.toLinearMap (basis 4) * basis 4 - basis 4 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_4_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL44 := hL (basis 4) (basis 4)
  rw [bmul_4_4] at hL44
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_4_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL44, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_4_5 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 4)) (basis 5) + splitBilinear (basis 4) (D.toLinearMap (basis 5)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 4)) (basis 5) + splitBilinear (basis 4) (D.toLinearMap (basis 5)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 1) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 4) := by
    simp only [bmul_1_1, bmul_1_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_1_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL14, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_4_6 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 4)) (basis 6) + splitBilinear (basis 4) (D.toLinearMap (basis 6)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 4)) (basis 6) + splitBilinear (basis 4) (D.toLinearMap (basis 6)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 1) + (1) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 4) := by
    simp only [bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL21, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_4_7 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 4)) (basis 7) + splitBilinear (basis 4) (D.toLinearMap (basis 7)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 4)) (basis 7) + splitBilinear (basis 4) (D.toLinearMap (basis 7)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 0) + (-1) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 4) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 5) := by
    simp only [bmul_1_6, bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL21, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_5_0 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 5)) (basis 0) + splitBilinear (basis 5) (D.toLinearMap (basis 0)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 5)) (basis 0) + splitBilinear (basis 5) (D.toLinearMap (basis 0)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 5) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 6) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 2) := by
    simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL34, hL24, hL16, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_5_1 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 5)) (basis 1) + splitBilinear (basis 5) (D.toLinearMap (basis 1)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 5)) (basis 1) + splitBilinear (basis 5) (D.toLinearMap (basis 1)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 7) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 3) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 3) := by
    simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL34, hL24, hL16, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_5_2 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 5)) (basis 2) + splitBilinear (basis 5) (D.toLinearMap (basis 2)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 5)) (basis 2) + splitBilinear (basis 5) (D.toLinearMap (basis 2)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 4) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL34, hL24, hL16, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_5_3 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 5)) (basis 3) + splitBilinear (basis 5) (D.toLinearMap (basis 3)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 5)) (basis 3) + splitBilinear (basis 5) (D.toLinearMap (basis 3)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 5) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 1) := by
    simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_4, bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL34, hL24, hL16, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_5_4 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 5)) (basis 4) + splitBilinear (basis 5) (D.toLinearMap (basis 4)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 5)) (basis 4) + splitBilinear (basis 5) (D.toLinearMap (basis 4)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 1) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 4) := by
    simp only [bmul_1_1, bmul_1_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_1_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL14, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_5_5 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 5)) (basis 5) + splitBilinear (basis 5) (D.toLinearMap (basis 5)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 5)) (basis 5) + splitBilinear (basis 5) (D.toLinearMap (basis 5)) = (2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 0) + (-1) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 0) + (2) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 5) + (1) * splitBilinear (D.toLinearMap (basis 4 * basis 4) - D.toLinearMap (basis 4) * basis 4 - basis 4 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_1_1, bmul_1_4, bmul_4_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL44 := hL (basis 4) (basis 4)
  rw [bmul_4_4] at hL44
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_1_4, bmul_4_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL14, hL44, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_5_6 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 5)) (basis 6) + splitBilinear (basis 5) (D.toLinearMap (basis 6)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 5)) (basis 6) + splitBilinear (basis 5) (D.toLinearMap (basis 6)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 6) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 5) := by
    simp only [bmul_1_4, bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_4, bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL21, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_5_7 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 5)) (basis 7) + splitBilinear (basis 5) (D.toLinearMap (basis 7)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 5)) (basis 7) + splitBilinear (basis 5) (D.toLinearMap (basis 7)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 1) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 7) + (-1) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 5) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 1) + (-1) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 4) := by
    simp only [bmul_1_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_2_1, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  simp only [bmul_1_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_2_1, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL24, hL16, hL12, hL21]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_6_0 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 6)) (basis 0) + splitBilinear (basis 6) (D.toLinearMap (basis 0)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 6)) (basis 0) + splitBilinear (basis 6) (D.toLinearMap (basis 0)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 6) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 5) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 0) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 1) := by
    simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL34, hL24, hL16, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_6_1 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 6)) (basis 1) + splitBilinear (basis 6) (D.toLinearMap (basis 1)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 6)) (basis 1) + splitBilinear (basis 6) (D.toLinearMap (basis 1)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 4) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_6_2 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 6)) (basis 2) + splitBilinear (basis 6) (D.toLinearMap (basis 2)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 6)) (basis 2) + splitBilinear (basis 6) (D.toLinearMap (basis 2)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 7) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 2) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 3) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_6_3 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 6)) (basis 3) + splitBilinear (basis 6) (D.toLinearMap (basis 3)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 6)) (basis 3) + splitBilinear (basis 6) (D.toLinearMap (basis 3)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 6) + (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 2) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 2) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_6_4 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 6)) (basis 4) + splitBilinear (basis 6) (D.toLinearMap (basis 4)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 6)) (basis 4) + splitBilinear (basis 6) (D.toLinearMap (basis 4)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 1) + (1) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 4) := by
    simp only [bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL21, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_6_5 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 6)) (basis 5) + splitBilinear (basis 6) (D.toLinearMap (basis 5)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 6)) (basis 5) + splitBilinear (basis 6) (D.toLinearMap (basis 5)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 6) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 5) := by
    simp only [bmul_1_4, bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_4, bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL21, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_6_6 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 6)) (basis 6) + splitBilinear (basis 6) (D.toLinearMap (basis 6)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 6)) (basis 6) + splitBilinear (basis 6) (D.toLinearMap (basis 6)) = (2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 0) + (-1) * splitBilinear (D.toLinearMap (basis 2 * basis 2) - D.toLinearMap (basis 2) * basis 2 - basis 2 * D.toLinearMap (basis 2)) (basis 0) + (2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 6) + (1) * splitBilinear (D.toLinearMap (basis 4 * basis 4) - D.toLinearMap (basis 4) * basis 4 - basis 4 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_2_2, bmul_2_4, bmul_4_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL22 := hL (basis 2) (basis 2)
  rw [bmul_2_2] at hL22
  have map_neg_2_2 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_2_2] at hL22
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL44 := hL (basis 4) (basis 4)
  rw [bmul_4_4] at hL44
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_2_2, bmul_2_4, bmul_4_4, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL22, hL24, hL44, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_6_7 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 6)) (basis 7) + splitBilinear (basis 6) (D.toLinearMap (basis 7)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 6)) (basis 7) + splitBilinear (basis 6) (D.toLinearMap (basis 7)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 1) + (-1) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 6) := by
    simp only [bmul_1_1, bmul_1_6, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_1_6, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL16, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_7_0 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 7)) (basis 0) + splitBilinear (basis 7) (D.toLinearMap (basis 0)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 7)) (basis 0) + splitBilinear (basis 7) (D.toLinearMap (basis 0)) = (-1) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 7) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 4) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 1) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_3_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL34, hL24, hL16, hL12, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_7_1 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 7)) (basis 1) + splitBilinear (basis 7) (D.toLinearMap (basis 1)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 7)) (basis 1) + splitBilinear (basis 7) (D.toLinearMap (basis 1)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 5) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 0) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 1) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_7_2 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 7)) (basis 2) + splitBilinear (basis 7) (D.toLinearMap (basis 2)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 7)) (basis 2) + splitBilinear (basis 7) (D.toLinearMap (basis 2)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 6) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 2) + (1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 3) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 2) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_7_3 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 7)) (basis 3) + splitBilinear (basis 7) (D.toLinearMap (basis 3)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 7)) (basis 3) + splitBilinear (basis 7) (D.toLinearMap (basis 3)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 7) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 3) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 2) + (1 / 2) * splitBilinear (D.toLinearMap (basis 3 * basis 4) - D.toLinearMap (basis 3) * basis 4 - basis 3 * D.toLinearMap (basis 4)) (basis 3) := by
    simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL34 := hL (basis 3) (basis 4)
  rw [bmul_3_4] at hL34
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_3_4, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL34, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_7_4 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 7)) (basis 4) + splitBilinear (basis 7) (D.toLinearMap (basis 4)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 7)) (basis 4) + splitBilinear (basis 7) (D.toLinearMap (basis 4)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 0) + (-1) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 4) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 0) + (1) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 5) := by
    simp only [bmul_1_6, bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  simp only [bmul_1_6, bmul_2_1, bmul_2_4, bmul_1_2, map_neg, map_add, map_sub, map_smul]
  rw [hL16, hL21, hL24, hL12]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_7_5 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 7)) (basis 5) + splitBilinear (basis 7) (D.toLinearMap (basis 5)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 7)) (basis 5) + splitBilinear (basis 7) (D.toLinearMap (basis 5)) = (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 2) - D.toLinearMap (basis 1) * basis 2 - basis 1 * D.toLinearMap (basis 2)) (basis 1) + (1) * splitBilinear (D.toLinearMap (basis 1 * basis 4) - D.toLinearMap (basis 1) * basis 4 - basis 1 * D.toLinearMap (basis 4)) (basis 7) + (-1) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 5) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 2 * basis 1) - D.toLinearMap (basis 2) * basis 1 - basis 2 * D.toLinearMap (basis 1)) (basis 1) + (-1) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 4) := by
    simp only [bmul_1_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_2_1, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL14 := hL (basis 1) (basis 4)
  rw [bmul_1_4] at hL14
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL12 := hL (basis 1) (basis 2)
  rw [bmul_1_2] at hL12
  have hL21 := hL (basis 2) (basis 1)
  rw [bmul_2_1] at hL21
  have map_neg_2_1 : D.toLinearMap (-basis 3) = - D.toLinearMap (basis 3) := map_neg D.toLinearMap (basis 3)
  rw [map_neg_2_1] at hL21
  simp only [bmul_1_4, bmul_2_4, bmul_1_6, bmul_1_2, bmul_2_1, map_neg, map_add, map_sub, map_smul]
  rw [hL14, hL24, hL16, hL12, hL21]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_7_6 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 7)) (basis 6) + splitBilinear (basis 7) (D.toLinearMap (basis 6)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 7)) (basis 6) + splitBilinear (basis 7) (D.toLinearMap (basis 6)) = (1 / 2) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 1) + (-1 / 2) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 1) + (-1) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 6) := by
    simp only [bmul_1_1, bmul_1_6, bmul_0_0, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  simp only [bmul_1_1, bmul_1_6, bmul_0_0, map_neg, map_add, map_sub, map_smul]
  rw [hL11, hL16, hL00]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

lemma skew_proof_7_7 (D : OctDerivation) :
  splitBilinear (D.toLinearMap (basis 7)) (basis 7) + splitBilinear (basis 7) (D.toLinearMap (basis 7)) = 0 := by
  have H : splitBilinear (D.toLinearMap (basis 7)) (basis 7) + splitBilinear (basis 7) (D.toLinearMap (basis 7)) = (3) * splitBilinear (D.toLinearMap (basis 0 * basis 0) - D.toLinearMap (basis 0) * basis 0 - basis 0 * D.toLinearMap (basis 0)) (basis 0) + (-1) * splitBilinear (D.toLinearMap (basis 1 * basis 1) - D.toLinearMap (basis 1) * basis 1 - basis 1 * D.toLinearMap (basis 1)) (basis 0) + (-2) * splitBilinear (D.toLinearMap (basis 1 * basis 6) - D.toLinearMap (basis 1) * basis 6 - basis 1 * D.toLinearMap (basis 6)) (basis 7) + (-1) * splitBilinear (D.toLinearMap (basis 2 * basis 2) - D.toLinearMap (basis 2) * basis 2 - basis 2 * D.toLinearMap (basis 2)) (basis 0) + (2) * splitBilinear (D.toLinearMap (basis 2 * basis 4) - D.toLinearMap (basis 2) * basis 4 - basis 2 * D.toLinearMap (basis 4)) (basis 6) + (1) * splitBilinear (D.toLinearMap (basis 4 * basis 4) - D.toLinearMap (basis 4) * basis 4 - basis 4 * D.toLinearMap (basis 4)) (basis 0) := by
    simp only [bmul_2_4, bmul_1_6, bmul_0_0, bmul_2_2, bmul_1_1, bmul_4_4, map_neg, map_add, map_sub, map_smul]
    dsimp [splitBilinear, splitNorm, basis, mul_def, star]
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
               Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero]
    ring_nf
  rw [H]
  have hL : ∀ x y, D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y = 0 := by
    intro x y
    have H2 := D.leibniz' x y
    calc D.toLinearMap (x * y) - D.toLinearMap x * y - x * D.toLinearMap y
      _ = (D.toLinearMap x * y + x * D.toLinearMap y) - D.toLinearMap x * y - x * D.toLinearMap y := by rw [H2]
      _ = 0 := by abel
  have hL24 := hL (basis 2) (basis 4)
  rw [bmul_2_4] at hL24
  have hL16 := hL (basis 1) (basis 6)
  rw [bmul_1_6] at hL16
  have map_neg_1_6 : D.toLinearMap (-basis 7) = - D.toLinearMap (basis 7) := map_neg D.toLinearMap (basis 7)
  rw [map_neg_1_6] at hL16
  have hL00 := hL (basis 0) (basis 0)
  rw [bmul_0_0] at hL00
  have hL22 := hL (basis 2) (basis 2)
  rw [bmul_2_2] at hL22
  have map_neg_2_2 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_2_2] at hL22
  have hL11 := hL (basis 1) (basis 1)
  rw [bmul_1_1] at hL11
  have map_neg_1_1 : D.toLinearMap (-basis 0) = - D.toLinearMap (basis 0) := map_neg D.toLinearMap (basis 0)
  rw [map_neg_1_1] at hL11
  have hL44 := hL (basis 4) (basis 4)
  rw [bmul_4_4] at hL44
  simp only [bmul_2_4, bmul_1_6, bmul_0_0, bmul_2_2, bmul_1_1, bmul_4_4, map_neg, map_add, map_sub, map_smul]
  rw [hL24, hL16, hL00, hL22, hL11, hL44]
  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
  simp only [h_bilin_zero, mul_zero, add_zero, neg_zero]

theorem derivation_is_skew_basis (D : OctDerivation) (i j : Fin 8) :
  splitBilinear (D.toLinearMap (basis i)) (basis j) + splitBilinear (basis i) (D.toLinearMap (basis j)) = 0 := by
  fin_cases i <;> fin_cases j
  · exact skew_proof_0_0 D
  · exact skew_proof_0_1 D
  · exact skew_proof_0_2 D
  · exact skew_proof_0_3 D
  · exact skew_proof_0_4 D
  · exact skew_proof_0_5 D
  · exact skew_proof_0_6 D
  · exact skew_proof_0_7 D
  · exact skew_proof_1_0 D
  · exact skew_proof_1_1 D
  · exact skew_proof_1_2 D
  · exact skew_proof_1_3 D
  · exact skew_proof_1_4 D
  · exact skew_proof_1_5 D
  · exact skew_proof_1_6 D
  · exact skew_proof_1_7 D
  · exact skew_proof_2_0 D
  · exact skew_proof_2_1 D
  · exact skew_proof_2_2 D
  · exact skew_proof_2_3 D
  · exact skew_proof_2_4 D
  · exact skew_proof_2_5 D
  · exact skew_proof_2_6 D
  · exact skew_proof_2_7 D
  · exact skew_proof_3_0 D
  · exact skew_proof_3_1 D
  · exact skew_proof_3_2 D
  · exact skew_proof_3_3 D
  · exact skew_proof_3_4 D
  · exact skew_proof_3_5 D
  · exact skew_proof_3_6 D
  · exact skew_proof_3_7 D
  · exact skew_proof_4_0 D
  · exact skew_proof_4_1 D
  · exact skew_proof_4_2 D
  · exact skew_proof_4_3 D
  · exact skew_proof_4_4 D
  · exact skew_proof_4_5 D
  · exact skew_proof_4_6 D
  · exact skew_proof_4_7 D
  · exact skew_proof_5_0 D
  · exact skew_proof_5_1 D
  · exact skew_proof_5_2 D
  · exact skew_proof_5_3 D
  · exact skew_proof_5_4 D
  · exact skew_proof_5_5 D
  · exact skew_proof_5_6 D
  · exact skew_proof_5_7 D
  · exact skew_proof_6_0 D
  · exact skew_proof_6_1 D
  · exact skew_proof_6_2 D
  · exact skew_proof_6_3 D
  · exact skew_proof_6_4 D
  · exact skew_proof_6_5 D
  · exact skew_proof_6_6 D
  · exact skew_proof_6_7 D
  · exact skew_proof_7_0 D
  · exact skew_proof_7_1 D
  · exact skew_proof_7_2 D
  · exact skew_proof_7_3 D
  · exact skew_proof_7_4 D
  · exact skew_proof_7_5 D
  · exact skew_proof_7_6 D
  · exact skew_proof_7_7 D

