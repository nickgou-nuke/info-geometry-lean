import Mathlib
import proofs.SplitOctonionAlternativity

open SplitOctonion
open Quaternion

lemma left_linearized_alternative' (α x y : SplitOct) :
  α * (x * y) = (α * x) * y + (x * α) * y - x * (α * y) := by
  ext1 <;> ext1 <;> {
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def]
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
      Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
    ring
  }

lemma right_linearized_alternative' (x y β : SplitOct) :
  (x * y) * β = x * (y * β) - (x * β) * y + x * (β * y) := by
  ext1 <;> ext1 <;> {
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def]
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
      Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
    ring
  }
