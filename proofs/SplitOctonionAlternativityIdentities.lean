import Mathlib
import proofs.SplitOctonionQuaternionChart

open SplitOctonion
open Quaternion


lemma left_alternative (x y : SplitOct) : x * (x * y) = (x * x) * y := by
  ext1 <;> ext1 <;> {
    dsimp [mul_def, add_def, sub_def, neg_def, star]
    simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_add, imI_add,
      imJ_add, imK_add]
    ring
  }
