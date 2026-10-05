import re

file_path = "lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean"
with open(file_path, "r") as f:
    content = f.read()

content = content.replace("try ring_nf <;> try ring <;> try norm_num", "try exact chiral_helper_1 <;> try ring_nf <;> try ring <;> try norm_num")

with open(file_path, "w") as f:
    f.write(content)

