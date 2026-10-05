with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

content = content.replace(
    "    try apply Quaternion.ext <;>\n      try rw [Quaternion.ext_iff] <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try { repeat constructor } <;>\n      try ring",
    "    ext <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try ring"
)

content = content.replace(
    "    try apply Quaternion.ext <;>\n      try rw [Quaternion.ext_iff] <;>\n      try { repeat constructor } <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul, chiral_helper_1] <;>\n      try ring",
    "    ext <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul, chiral_helper_1] <;>\n      try ring"
)

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
