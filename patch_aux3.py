import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

target = """            have h_eq : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (axialFlowCoordinate t x) (by rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate]; exact hproj_aux) := congr_arg Subtype.val this
            rw [h_eq]
            congr 1
            exact congrFun (axialFlowCoordinate_eq_hyperbolicFlowCoordinate t) x"""

replacement = """            have h_eq : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (axialFlowCoordinate t x) (by rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate]; exact hproj_aux) := congr_arg Subtype.val this
            rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate t] at h_eq
            exact h_eq"""

text = text.replace(target, replacement)

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

