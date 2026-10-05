import re

with open('lean/InfoGeometry/Core/UnifiedGeometry.lean', 'r') as f:
    content = f.read()

content = content.replace('_ = (-1 : ℝ) • ⁅A, B⁆ := by simp', '_ = (-1 : ℝ) • ⁅A, B⁆ := by simp [lie_smul, smul_lie]')
content = content.replace('_ = (1 : ℝ) • ⁅A, B⁆ := by simp', '_ = (1 : ℝ) • ⁅A, B⁆ := by simp [lie_smul, smul_lie]')

with open('lean/InfoGeometry/Core/UnifiedGeometry.lean', 'w') as f:
    f.write(content)
