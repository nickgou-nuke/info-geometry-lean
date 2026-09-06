import Mathlib
import proofs.SplitOctonionQuaternionChart
import proofs.SplitOctonionAlgebra

set_option linter.unusedSimpArgs false

open SplitOctonion
open Quaternion

lemma left_alternative (x y : SplitOct) : x * (x * y) = (x * x) * y := by
  ext1 <;> ext1 <;> {
    dsimp [mul_def, add_def, sub_def, neg_def, star]
    simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub, imJ_sub, imK_sub, re_neg, imI_neg, imJ_neg, imK_neg]
    ring
  }

lemma right_alternative (x y : SplitOct) : (x * y) * y = x * (y * y) := by
  ext1 <;> ext1 <;> {
    dsimp [mul_def, add_def, sub_def, neg_def, star]
    simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub, imJ_sub, imK_sub, re_neg, imI_neg, imJ_neg, imK_neg]
    ring
  }

lemma left_linearized_alternative (x y z : SplitOct) : x * (y * z) + y * (x * z) = (x * y + y * x) * z := by
  have h1 := left_alternative (x + y) z
  have h2 := left_alternative x z
  have h3 := left_alternative y z
  calc
    x * (y * z) + y * (x * z) = (x + y) * ((x + y) * z) - x * (x * z) - y * (y * z) := by
      simp only [add_mul, mul_add]
      abel
    _ = ((x + y) * (x + y)) * z - (x * x) * z - (y * y) * z := by
      rw [h1, h2, h3]
    _ = (x * y + y * x) * z := by
      simp only [add_mul, mul_add]
      abel

lemma right_linearized_alternative (x y z : SplitOct) : (x * y) * z + (x * z) * y = x * (y * z + z * y) := by
  have h1 := right_alternative x (y + z)
  have h2 := right_alternative x y
  have h3 := right_alternative x z
  calc
    (x * y) * z + (x * z) * y = (x * (y + z)) * (y + z) - (x * y) * y - (x * z) * z := by
      simp only [add_mul, mul_add]
      abel
    _ = x * ((y + z) * (y + z)) - x * (y * y) - x * (z * z) := by
      rw [h1, h2, h3]
    _ = x * (y * z + z * y) := by
      simp only [add_mul, mul_add]
      abel

lemma associator_swap_left (x y z : SplitOct) : (x * y) * z - x * (y * z) = - ((y * x) * z - y * (x * z)) := by
  have h := left_linearized_alternative x y z
  have h2 : x * (y * z) + y * (x * z) = (x * y) * z + (y * x) * z := by
    rw [h, add_mul]
  calc
    (x * y) * z - x * (y * z) = (x * y) * z + (y * x) * z - x * (y * z) - (y * x) * z := by abel
    _ = x * (y * z) + y * (x * z) - x * (y * z) - (y * x) * z := by rw [<- h2]
    _ = - ((y * x) * z - y * (x * z)) := by abel
