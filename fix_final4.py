import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

target1 = """      · rintro (h | h | ⟨h, h04⟩)
        · apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Real.exp t, ?_⟩
          rw [hyperbolicFlow_on_positiveWeight t x h]
        · apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Real.exp (-t), ?_⟩
          rw [hyperbolicFlow_on_negativeWeight t x h]
        · apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨1, ?_⟩
          rw [hyperbolicFlow_on_zeroWeight t x h]
          simp"""

replacement1 = """      · rintro (h | h | ⟨h, h04⟩)
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Real.exp t, ?_⟩
          rw [hyperbolicFlow_on_positiveWeight t x h]
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Real.exp (-t), ?_⟩
          rw [hyperbolicFlow_on_negativeWeight t x h]
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨1, ?_⟩
          rw [hyperbolicFlow_on_zeroWeight t x h]
          simp"""

text = text.replace(target1, replacement1)

text = text.replace("(by simp)", "(by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])")
text = text.replace("(by simp [Real.exp_neg])", "(by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight, Real.exp_neg])")

# Also the ha' missing for `a ≠ 1` when a = Real.exp(-t) and t ≠ 0
# `simpa [ha']` might not know Real.exp (-t) ≠ 1 because t ≠ 0.
# Real.exp y = 1 ↔ y = 0.
# So we need `have : Real.exp (-t) ≠ 1 := by intro H; have := Real.exp_injective H; linarith`
# Wait! In Mathlib, `Real.exp_ne_one_iff` is `x ≠ 0`.
text = text.replace("(kill 4 1 (by simpa [ha'])", "(kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith)")
text = text.replace("(kill 0 1 (by simpa [ha'])", "(kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith)")


with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

