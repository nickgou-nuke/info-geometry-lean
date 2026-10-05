import re

file_path = "lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean"
with open(file_path, "r") as f:
    content = f.read()

content = content.replace("try field_simp <;> try ring", "try field_simp <;> try ring <;> show (2:ℝ)⁻¹ * (-1 + -1) = -1 <;> rfl")

with open(file_path, "w") as f:
    f.write(content)

