import re

file_path = "lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean"
with open(file_path, "r") as f:
    content = f.read()

content = content.replace("theorem chiralStar_uOne_vOne", "set_option pp.all true\ntheorem chiralStar_uOne_vOne")

with open(file_path, "w") as f:
    f.write(content)

