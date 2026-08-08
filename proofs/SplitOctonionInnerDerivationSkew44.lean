import Mathlib
import proofs.SplitOctonionNorm44
import proofs.SplitOctonionInnerDerivation

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionInnerDerivation
open Quaternion

lemma innerDeriv_skew_adjoint (x y u v : SplitOct) :
  splitBilinear (innerDeriv x y u) v + splitBilinear u (innerDeriv x y v) = 0 := by
  dsimp [splitBilinear, splitNorm, innerDeriv, associator, bracket, add_def, sub_def, smul_def, mul_def, star, neg_def]
  ext
  · simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
               Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
               Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
               Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul]
    ring
