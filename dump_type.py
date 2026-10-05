with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

content = content.replace('      try field_simp <;> try ring <;>\n      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul]',
'''      exact "TYPE_DUMP"''')

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
