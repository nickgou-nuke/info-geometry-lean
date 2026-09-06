import Mathlib
import proofs.SplitOctonionAlgebra

open SplitOctonion
open Quaternion

def is_middle_nucleus (b : SplitOct) : Prop :=
  ∀ x y : SplitOct, (x * b) * y = x * (b * y)

def e1 : SplitOct := { a := { re := 0, imI := 1, imJ := 0, imK := 0 }, b := 0 }
def e2 : SplitOct := { a := { re := 0, imI := 0, imJ := 1, imK := 0 }, b := 0 }
def e3 : SplitOct := { a := { re := 0, imI := 0, imJ := 0, imK := 1 }, b := 0 }
def e4 : SplitOct := { a := 0, b := { re := 1, imI := 0, imJ := 0, imK := 0 } }
def e5 : SplitOct := { a := 0, b := { re := 0, imI := 1, imJ := 0, imK := 0 } }
def e6 : SplitOct := { a := 0, b := { re := 0, imI := 0, imJ := 1, imK := 0 } }
def e7 : SplitOct := { a := 0, b := { re := 0, imI := 0, imJ := 0, imK := 1 } }

lemma middleNucleus_is_real (b : SplitOct) (h : is_middle_nucleus b) :
  b.a.imI = 0 ∧ b.a.imJ = 0 ∧ b.a.imK = 0 ∧ b.b.re = 0 ∧ b.b.imI = 0 ∧ b.b.imJ = 0 ∧ b.b.imK = 0 := by
  have eq1 : b.a.imI = 0 := by
    have h1 := h e2 e4
    have h1_k := congr_arg (fun x : SplitOct => x.b.imK) h1
    dsimp [e2, e4] at h1_k
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def] at h1_k
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
               Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
               Quaternion.mul_re, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
               Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK,
               Quaternion.one_re, Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK] at h1_k
    ring_nf at h1_k
    linarith [h1_k]

  have eq2 : b.a.imJ = 0 := by
    have h2 := h e3 e4
    have h2_k := congr_arg (fun x : SplitOct => x.b.imI) h2
    dsimp [e3, e4] at h2_k
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def] at h2_k
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
               Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
               Quaternion.mul_re, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
               Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK,
               Quaternion.one_re, Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK] at h2_k
    ring_nf at h2_k
    linarith [h2_k]

  have eq3 : b.a.imK = 0 := by
    have h3 := h e1 e4
    have h3_k := congr_arg (fun x : SplitOct => x.b.imJ) h3
    dsimp [e1, e4] at h3_k
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def] at h3_k
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
               Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
               Quaternion.mul_re, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
               Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK,
               Quaternion.one_re, Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK] at h3_k
    ring_nf at h3_k
    linarith [h3_k]

  have eq4 : b.b.re = 0 := by
    have h4 := h e1 e2
    have h4_k := congr_arg (fun x : SplitOct => x.b.imK) h4
    dsimp [e1, e2] at h4_k
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def] at h4_k
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
               Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
               Quaternion.mul_re, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
               Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK,
               Quaternion.one_re, Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK] at h4_k
    ring_nf at h4_k
    linarith [h4_k]

  have eq5 : b.b.imI = 0 := by
    have h5 := h e2 e1
    have h5_k := congr_arg (fun x : SplitOct => x.b.imJ) h5
    dsimp [e2, e1] at h5_k
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def] at h5_k
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
               Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
               Quaternion.mul_re, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
               Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK,
               Quaternion.one_re, Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK] at h5_k
    ring_nf at h5_k
    linarith [h5_k]

  have eq6 : b.b.imJ = 0 := by
    have h6 := h e1 e3
    have h6_k := congr_arg (fun x : SplitOct => x.b.re) h6
    dsimp [e1, e3] at h6_k
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def] at h6_k
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
               Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
               Quaternion.mul_re, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
               Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK,
               Quaternion.one_re, Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK] at h6_k
    ring_nf at h6_k
    linarith [h6_k]

  have eq7 : b.b.imK = 0 := by
    have h7 := h e1 e5
    have h7_k := congr_arg (fun x : SplitOct => x.a.imK) h7
    dsimp [e1, e5] at h7_k
    simp only [add_def, mul_def, star, smul_def, sub_def, neg_def] at h7_k
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
               Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
               Quaternion.mul_re, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
               Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
               Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK,
               Quaternion.one_re, Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK] at h7_k
    ring_nf at h7_k
    linarith [h7_k]

  exact ⟨eq1, eq2, eq3, eq4, eq5, eq6, eq7⟩

theorem middleNucleus_eq_scalar (b : SplitOct) (h : is_middle_nucleus b) :
  b = { a := { re := b.a.re, imI := 0, imJ := 0, imK := 0 }, b := 0 } := by
  have ⟨h1, h2, h3, h4, h5, h6, h7⟩ := middleNucleus_is_real b h
  ext1 <;> ext1
  · rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
