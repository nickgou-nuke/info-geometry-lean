import re

with open('lean/InfoGeometry/Core/UnifiedGeometry.lean', 'r') as f:
    content = f.read()

# Add import
content = content.replace('import InfoGeometry.Architecture.SymmetricSpace', 'import InfoGeometry.Architecture.SymmetricSpace\nimport Mathlib.Algebra.Lie.OfAssociative')

# Add local instances
old = """theorem conjugationMapNeg_bracket (J : V →L[ℝ] V)
    (hJ : J.comp J = -ContinuousLinearMap.id ℝ V)
    (A B : V →L[ℝ] V) :"""

new = """local instance : LieRing (V →L[ℝ] V) := Ring.lieRing
local instance : LieAlgebra ℝ (V →L[ℝ] V) := LieAlgebra.ofAssociativeAlgebra

theorem conjugationMapNeg_bracket (J : V →L[ℝ] V)
    (hJ : J.comp J = -ContinuousLinearMap.id ℝ V)
    (A B : V →L[ℝ] V) :"""

content = content.replace(old, new)

with open('lean/InfoGeometry/Core/UnifiedGeometry.lean', 'w') as f:
    f.write(content)
