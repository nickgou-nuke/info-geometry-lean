import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

target = """          have aux : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux := by
            have := circularNullBoundaryFlow_mk_axialFlow t x hx hp
            exact congr_arg Subtype.val this"""

replacement = """          have aux : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux := by
            have := circularNullBoundaryFlow_mk_axialFlow t x hx hp
            have h_eq : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (axialFlowCoordinate t x) (by rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate]; exact hproj_aux) := congr_arg Subtype.val this
            rw [h_eq]
            congr 1
            exact axialFlowCoordinate_eq_hyperbolicFlowCoordinate t x"""

text = text.replace(target, replacement)

# Also fix the unused simp warnings
text = text.replace("simp [Units.smul_def, hu_ne]", "simp [hu_ne]")

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

