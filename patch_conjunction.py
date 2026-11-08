with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

# For line 69
content = content.replace(
    "    try apply Quaternion.ext <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n        ring",
    "    try apply Quaternion.ext <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul, ext_iff] <;>\n      try { repeat constructor } <;>\n      ring"
)

# For line 1136 and 1145
content = content.replace(
    "    try apply Quaternion.ext <;>\n      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul]",
    "    try apply Quaternion.ext <;>\n      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul, ext_iff] <;>\n      try { repeat constructor } <;>\n      norm_num"
)

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
