with open("sandbox/MobiusGeometry.lean", "r") as f:
    text = f.read()

import re

new_proof = """lemma mobius_unique_01inf (M : MobiusTransform) (h0 : M.eval (some 0) = some 0)
    (h1 : M.eval (some 1) = some 1) (hinf : M.eval none = none) :
    ∀ z, M.eval z = z := by
  have hc : M.c = 0 := by
    dsimp [MobiusTransform.eval] at hinf
    split_ifs at hinf with h
    · exact h
    · cases hinf
  have hb : M.b = 0 := by
    dsimp [MobiusTransform.eval] at h0
    have hdenom : M.c * 0 + M.d = M.d := by ring
    rw [hdenom] at h0
    split_ifs at h0 with hd
    · cases h0
    · injection h0 with h0'
      have hnum : M.a * 0 + M.b = M.b := by ring
      rw [hnum] at h0'
      exact div_eq_zero_iff.mp h0' |>.resolve_right hd
  have had : M.a = M.d := by
    dsimp [MobiusTransform.eval] at h1
    have hdenom : M.c * 1 + M.d = M.d := by rw [hc, zero_mul, zero_add]
    rw [hdenom] at h1
    split_ifs at h1 with hd
    · cases h1
    · injection h1 with h1'
      have hnum : M.a * 1 + M.b = M.a := by rw [hb, mul_one, add_zero]
      rw [hnum] at h1'
      exact div_eq_iff_mul_eq hd |>.mp h1' |> (·.trans (one_mul M.d).symm)
  have hd_ne : M.d ≠ 0 := by
    intro hd
    have hdet := M.det_ne_zero
    rw [hc, hb, hd, had, mul_zero, mul_zero, sub_zero] at hdet
    exact hdet rfl
  intro z
  cases z with
  | none =>
      dsimp [MobiusTransform.eval]
      rw [if_pos hc]
  | some z' =>
      dsimp [MobiusTransform.eval]
      have hdenom : M.c * z' + M.d = M.d := by rw [hc, zero_mul, zero_add]
      rw [hdenom]
      have hnum : M.a * z' + M.b = M.d * z' := by rw [hb, had, add_zero]
      rw [hnum]
      rw [if_neg hd_ne]
      congr 1
      rw [mul_comm]
      exact mul_div_cancel_right₀ z' hd_ne"""

text = re.sub(r"lemma mobius_unique_01inf[\s\S]+?exact mul_div_cancel_right₀ z' hd_ne", new_proof, text)

with open("sandbox/MobiusGeometry.lean", "w") as f:
    f.write(text)

