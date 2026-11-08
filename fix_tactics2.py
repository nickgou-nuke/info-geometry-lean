import re

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

# For lines 1141 and 1151, replace try ring <;> norm_num... with try field_simp <;> try ring <;> norm_num
content = content.replace('      try ring <;>\n      norm_num [Quaternion.re_mul', '      try field_simp <;> try ring <;>\n      norm_num [Quaternion.re_mul')

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
