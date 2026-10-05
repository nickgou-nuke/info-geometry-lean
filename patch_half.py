import re

file_path = "lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean"
with open(file_path, "r") as f:
    content = f.read()

content = content.replace("private def half : ChiralEntry := (1 / 2 : ℝ) • entryOne", "private def half : ChiralEntry := ( (2:ℝ)⁻¹ ) • entryOne")

with open(file_path, "w") as f:
    f.write(content)

