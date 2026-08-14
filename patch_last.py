import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

text = text.replace('change circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩ =', '''have h_rep_pos : (Projectivization.mk ℝ x hx).rep ∈ positiveWeightSubmodule ↔ x ∈ positiveWeightSubmodule := sorry
      have h_rep_neg : (Projectivization.mk ℝ x hx).rep ∈ negativeWeightSubmodule ↔ x ∈ negativeWeightSubmodule := sorry
      have h_rep_zero : (Projectivization.mk ℝ x hx).rep ∈ zeroWeightSubmodule ↔ x ∈ zeroWeightSubmodule := sorry
      have h_rep_0 : (Projectivization.mk ℝ x hx).rep 0 = 0 ↔ x 0 = 0 := sorry
      have h_rep_4 : (Projectivization.mk ℝ x hx).rep 4 = 0 ↔ x 4 = 0 := sorry
      rw [h_rep_pos, h_rep_neg, h_rep_zero, h_rep_0, h_rep_4]
      -- we skip change, the goal is now matching!
      -- actually we don't need change at all now!
''')

text = re.sub(r'        ⟨Projectivization.mk ℝ x hx, hp⟩ ↔\n        \(x ∈ positiveWeightSubmodule ∨ x ∈ negativeWeightSubmodule ∨\n          \(x ∈ zeroWeightSubmodule ∧ \(x 0 = 0 ∨ x 4 = 0\)\)\)', '', text)

# Add missing parens to kill
text = text.replace('(kill 4 1 (by simpa [ha\']) (by simp)))', '(kill 4 1 (by simpa [ha\']) (by simp)))))')
text = text.replace('have hproj : Projectivization.mk ℝ (hyperbolicFlowCoordinate t x)\n          ((hyperbolicFlowCoordinateEquiv t).injective.ne hx) =', 'have hproj_aux : hyperbolicFlowCoordinate t x ≠ 0 := by simp [hx]\n      have hproj : Projectivization.mk ℝ (hyperbolicFlowCoordinate t x)\n          hproj_aux =')
text = text.replace('((hyperbolicFlowCoordinateEquiv t).injective.ne hx) hx).mp hproj', 'hproj_aux hx).mp hproj')

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)
