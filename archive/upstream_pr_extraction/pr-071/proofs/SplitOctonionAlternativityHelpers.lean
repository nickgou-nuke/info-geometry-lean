import Mathlib
import proofs.SplitOctonionAlternativity

open SplitOctonion
open Quaternion

lemma left_linearized_alternative' (α x y : SplitOct) :
  α * (x * y) = (α * x) * y + (x * α) * y - x * (α * y) := by
  ext1 <;> ext1 <;> {
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def]
    simp only [Quaternion.add_re, Quaternion.add_imI, Quaternion.add_imJ, Quaternion.add_imK,
               Quaternion.sub_re, Quaternion.sub_imI, Quaternion.sub_imJ, Quaternion.sub_imK,
               Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK,
               Quaternion.neg_re, Quaternion.neg_imI, Quaternion.neg_imJ, Quaternion.neg_imK,
               Quaternion.smul_re, Quaternion.smul_imI, Quaternion.smul_imJ, Quaternion.smul_imK]
    ring
  }

lemma right_linearized_alternative' (x y β : SplitOct) :
  (x * y) * β = x * (y * β) - (x * β) * y + x * (β * y) := by
  ext1 <;> ext1 <;> {
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def]
    simp only [Quaternion.add_re, Quaternion.add_imI, Quaternion.add_imJ, Quaternion.add_imK,
               Quaternion.sub_re, Quaternion.sub_imI, Quaternion.sub_imJ, Quaternion.sub_imK,
               Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK,
               Quaternion.neg_re, Quaternion.neg_imI, Quaternion.neg_imJ, Quaternion.neg_imK,
               Quaternion.smul_re, Quaternion.smul_imI, Quaternion.smul_imJ, Quaternion.smul_imK]
    ring
  }
