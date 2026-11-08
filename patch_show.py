import re

file_path = "lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean"
with open(file_path, "r") as f:
    content = f.read()

content = content.replace("try ring_nf <;> try ring <;> try linarith <;> try norm_num", "show (2:ℝ)⁻¹ * (-1 + -1) = -1 <;> ring")

with open(file_path, "w") as f:
    f.write(content)

