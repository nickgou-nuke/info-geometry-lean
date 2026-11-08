import re

file_path = "lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean"
with open(file_path, "r") as f:
    content = f.read()

content = content.replace("try exact chiral_helper_1", "try exact chiral_helper_2")

with open(file_path, "w") as f:
    f.write(content)

