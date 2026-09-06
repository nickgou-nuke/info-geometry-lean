import Mathlib
import proofs.SplitOctonionDerivationSpace
import proofs.SplitOctonionNorm44
import proofs.SplitOctonionTrialityCore

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionTrialityCore
open Quaternion

namespace OctDerivation

lemma splitOct_sq_rel (x : SplitOct) :
  x * x = (2 * splitBilinear x 1) • x - (splitBilinear x x) • 1 := by
  ext1 <;> ext1 <;>
  dsimp [splitBilinear, splitNorm, mul_def, add_def, sub_def, neg_def, smul_def, one_def] <;>
  simp only [re_mul, imI_mul, imJ_mul, imK_mul,
             re_star, imI_star, imJ_star, imK_star] <;>
  ring

lemma splitOct_comm_rel (x y : SplitOct) :
  x * y + y * x = (2 * splitBilinear x 1) • y + (2 * splitBilinear y 1) • x - (2 * splitBilinear x y) • 1 := by
  ext1 <;> ext1 <;>
  dsimp [splitBilinear, splitNorm, mul_def, add_def, sub_def, neg_def, smul_def, one_def] <;>
  simp only [re_mul, imI_mul, imJ_mul, imK_mul,
             re_star, imI_star, imJ_star, imK_star] <;>
  ring

lemma splitBilinear_smul_left (c : ℝ) (x y : SplitOct) : splitBilinear (c • x) y = c * splitBilinear x y := by
  simp [splitBilinear, splitNorm, smul_def, add_def, sub_def, neg_def]
  ring

lemma splitBilinear_one_one : splitBilinear 1 1 = 1 := by
  dsimp [splitBilinear, splitNorm, one_def, add_def, sub_def, neg_def]
  ring

lemma derivation_one (D : OctDerivation) : D.toLinearMap 1 = 0 := by
  have h := D.leibniz' 1 1
  rw [mul_one, one_mul, mul_one] at h
  have h2 : D.toLinearMap 1 + 0 = D.toLinearMap 1 + D.toLinearMap 1 := by
    rw [add_zero]
    exact h
  exact add_left_cancel h2.symm

lemma derivation_is_skew_adjoint_aux (D : OctDerivation) (x : SplitOct) : splitBilinear (D.toLinearMap x) x = 0 := by
  have h_sq := D.leibniz' x x
  have h_sq2 : D.toLinearMap (x * x) = D.toLinearMap ((2 * splitBilinear x 1) • x - (splitBilinear x x) • 1) := by rw [splitOct_sq_rel]
  have h_Dsub : D.toLinearMap ((2 * splitBilinear x 1) • x - (splitBilinear x x) • 1) = D.toLinearMap ((2 * splitBilinear x 1) • x) - D.toLinearMap ((splitBilinear x x) • 1) := by rw [LinearMap.map_sub]
  have h_Dsmul1 : D.toLinearMap ((2 * splitBilinear x 1) • x) = (2 * splitBilinear x 1) • D.toLinearMap x := by rw [LinearMap.map_smul]
  have h_Dsmul2 : D.toLinearMap ((splitBilinear x x) • 1) = (splitBilinear x x) • D.toLinearMap 1 := by rw [LinearMap.map_smul]
  rw [h_Dsub, h_Dsmul1, h_Dsmul2, derivation_one, smul_zero, sub_zero] at h_sq2
  rw [h_sq2] at h_sq
  have h_comm := splitOct_comm_rel (D.toLinearMap x) x
  have h_sq_rev : D.toLinearMap x * x + x * D.toLinearMap x = (2 * splitBilinear x 1) • D.toLinearMap x := h_sq.symm
  rw [h_sq_rev] at h_comm
  have h_diff : (2 * splitBilinear (D.toLinearMap x) 1) • x - (2 * splitBilinear (D.toLinearMap x) x) • 1 = 0 := by
    calc (2 * splitBilinear (D.toLinearMap x) 1) • x - (2 * splitBilinear (D.toLinearMap x) x) • 1
      _ = ((2 * splitBilinear (D.toLinearMap x) 1) • x + (2 * splitBilinear x 1) • D.toLinearMap x - (2 * splitBilinear (D.toLinearMap x) x) • 1) - (2 * splitBilinear x 1) • D.toLinearMap x := by abel
      _ = (2 * splitBilinear x 1) • D.toLinearMap x - (2 * splitBilinear x 1) • D.toLinearMap x := by rw [←h_comm]
      _ = 0 := sub_self _
  have h_diff3 : (splitBilinear (D.toLinearMap x) 1) • x - (splitBilinear (D.toLinearMap x) x) • 1 = 0 := by
    have h_diff2 : (2 : ℝ) • ((splitBilinear (D.toLinearMap x) 1) • x - (splitBilinear (D.toLinearMap x) x) • 1) = 0 := by
      calc (2 : ℝ) • ((splitBilinear (D.toLinearMap x) 1) • x - (splitBilinear (D.toLinearMap x) x) • 1)
        _ = (2 : ℝ) • ((splitBilinear (D.toLinearMap x) 1) • x) - (2 : ℝ) • ((splitBilinear (D.toLinearMap x) x) • 1) := by rw [smul_sub]
        _ = (2 * splitBilinear (D.toLinearMap x) 1) • x - (2 * splitBilinear (D.toLinearMap x) x) • 1 := by rw [smul_smul, smul_smul]
        _ = 0 := h_diff
    rcases smul_eq_zero.mp h_diff2 with h2 | h2
    · norm_num at h2
    · exact h2
  have h1 : (splitBilinear (D.toLinearMap x) 1) • x = (splitBilinear (D.toLinearMap x) x) • (1 : SplitOct) := eq_of_sub_eq_zero h_diff3
  have hb : splitBilinear ((splitBilinear (D.toLinearMap x) 1) • x) 1 = splitBilinear ((splitBilinear (D.toLinearMap x) x) • (1 : SplitOct)) 1 := by rw [h1]
  rw [splitBilinear_smul_left, splitBilinear_smul_left, splitBilinear_one_one, mul_one] at hb
  have h2 : (splitBilinear (D.toLinearMap x) 1) • (x - (splitBilinear x 1) • 1) = 0 := by
    calc (splitBilinear (D.toLinearMap x) 1) • (x - (splitBilinear x 1) • 1)
      _ = (splitBilinear (D.toLinearMap x) 1) • x - (splitBilinear (D.toLinearMap x) 1 * splitBilinear x 1) • 1 := by
        rw [smul_sub, smul_smul]
      _ = (splitBilinear (D.toLinearMap x) x) • 1 - (splitBilinear (D.toLinearMap x) 1 * splitBilinear x 1) • 1 := by
        rw [h1]
      _ = (splitBilinear (D.toLinearMap x) x - splitBilinear (D.toLinearMap x) 1 * splitBilinear x 1) • 1 := by
        rw [sub_smul]
      _ = 0 := by
        rw [hb, sub_self, zero_smul]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · rw [h3] at hb
    rw [zero_mul] at hb
    exact hb.symm
  · have hDx : D.toLinearMap x = 0 := by
      rw [eq_of_sub_eq_zero h3, LinearMap.map_smul, derivation_one, smul_zero]
    rw [hDx]
    dsimp [splitBilinear, splitNorm, add_def, sub_def, neg_def]
    ring

theorem derivation_is_skew_adjoint (D : OctDerivation) (x y : SplitOct) :
    splitBilinear (D.toLinearMap x) y + splitBilinear x (D.toLinearMap y) = 0 := by
  have h1 := derivation_is_skew_adjoint_aux D (x + y)
  have h2 := derivation_is_skew_adjoint_aux D x
  have h3 := derivation_is_skew_adjoint_aux D y
  have hd_add : D.toLinearMap (x + y) = D.toLinearMap x + D.toLinearMap y := LinearMap.map_add D.toLinearMap x y
  change splitBilinear (D.toLinearMap (x + y)) (x + y) = 0 at h1
  rw [hd_add] at h1
  have h_bilin : splitBilinear (D.toLinearMap x + D.toLinearMap y) (x + y) =
                 splitBilinear (D.toLinearMap x) x + splitBilinear (D.toLinearMap x) y +
                 splitBilinear (D.toLinearMap y) x + splitBilinear (D.toLinearMap y) y := by
    dsimp [splitBilinear, splitNorm, add_def, sub_def, neg_def]
    ring
  rw [h_bilin] at h1
  have h1_sub : splitBilinear (D.toLinearMap x) y + splitBilinear (D.toLinearMap y) x = 0 := by
    calc splitBilinear (D.toLinearMap x) y + splitBilinear (D.toLinearMap y) x
      _ = splitBilinear (D.toLinearMap x) x + splitBilinear (D.toLinearMap x) y + splitBilinear (D.toLinearMap y) x + splitBilinear (D.toLinearMap y) y := by
        rw [h2, h3, zero_add, add_zero]
      _ = 0 := h1
  rw [splitBilinear_symmetric (D.toLinearMap y) x] at h1_sub
  exact h1_sub

end OctDerivation
