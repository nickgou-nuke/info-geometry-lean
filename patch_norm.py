import re

file_path = "lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean"
with open(file_path, "r") as f:
    content = f.read()

content = re.sub(r"try change \(2:ℝ\)⁻¹ \* \(-1 \+ -1\) = -1 <;>\n    try ring", "try norm_num", content)

with open(file_path, "w") as f:
    f.write(content)

