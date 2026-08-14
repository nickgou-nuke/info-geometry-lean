import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

new_block = '''obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep x hx
      have hu_ne : (u : ℝ) ≠ 0 := u.ne_zero
      have h_rep_pos : (Projectivization.mk ℝ x hx).rep ∈ positiveWeightSubmodule ↔ x ∈ positiveWeightSubmodule := by
        rw [← hu, Submodule.smul_mem_iff _ hu_ne]
      have h_rep_neg : (Projectivization.mk ℝ x hx).rep ∈ negativeWeightSubmodule ↔ x ∈ negativeWeightSubmodule := by
        rw [← hu, Submodule.smul_mem_iff _ hu_ne]
      have h_rep_zero : (Projectivization.mk ℝ x hx).rep ∈ zeroWeightSubmodule ↔ x ∈ zeroWeightSubmodule := by
        rw [← hu, Submodule.smul_mem_iff _ hu_ne]
      have h_rep_0 : (Projectivization.mk ℝ x hx).rep 0 = 0 ↔ x 0 = 0 := by
        rw [← hu]; simp [Units.smul_def, hu_ne]
      have h_rep_4 : (Projectivization.mk ℝ x hx).rep 4 = 0 ↔ x 4 = 0 := by
        rw [← hu]; simp [Units.smul_def, hu_ne]
      rw [h_rep_pos, h_rep_neg, h_rep_zero, h_rep_0, h_rep_4]'''

text = text.replace('''have h_rep_pos : (Projectivization.mk ℝ x hx).rep ∈ positiveWeightSubmodule ↔ x ∈ positiveWeightSubmodule := sorry
      have h_rep_neg : (Projectivization.mk ℝ x hx).rep ∈ negativeWeightSubmodule ↔ x ∈ negativeWeightSubmodule := sorry
      have h_rep_zero : (Projectivization.mk ℝ x hx).rep ∈ zeroWeightSubmodule ↔ x ∈ zeroWeightSubmodule := sorry
      have h_rep_0 : (Projectivization.mk ℝ x hx).rep 0 = 0 ↔ x 0 = 0 := sorry
      have h_rep_4 : (Projectivization.mk ℝ x hx).rep 4 = 0 ↔ x 4 = 0 := sorry
      rw [h_rep_pos, h_rep_neg, h_rep_zero, h_rep_0, h_rep_4]''', new_block)

text = text.replace('-- we skip change, the goal is now matching!\n      -- actually we don\'t need change at all now!\n', '')

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

