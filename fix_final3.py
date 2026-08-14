import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

target1 = """      · rintro (h | h | ⟨h, h04⟩)
        · apply hproj.mpr
          have H := projective_positiveWeight_fixed t x hx h
          exact congr_arg Subtype.val H
        · apply hproj.mpr
          have H := projective_negativeWeight_fixed t x hx h
          exact congr_arg Subtype.val H
        · apply hproj.mpr
          rw [circularNullBoundaryFlow_mk_axialFlow]
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Units.mk0 1 one_ne_zero, ?_⟩
          rw [hyperbolicFlow_on_zeroWeight t x h]
          simp [Units.smul_def]"""

replacement1 = """      · rintro (h | h | ⟨h, h04⟩)
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

text = text.replace(target1, replacement1)

target2 = "have hz := memZero (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)"
replacement2 = "have hz := memZero (y := x) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)"

text = text.replace(target2, replacement2)

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

