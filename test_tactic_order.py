with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

content = content.replace(
    "    try apply Quaternion.ext <;>\n      try rw [Quaternion.ext_iff] <;>\n      try { repeat constructor } <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try ring",
    "    try apply Quaternion.ext <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try { repeat constructor } <;>\n      try ring"
)

content = content.replace(
    "    try apply Quaternion.ext <;>\n      try rw [Quaternion.ext_iff] <;>\n      try { repeat constructor } <;>\n      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try ring",
    "    try apply Quaternion.ext <;>\n      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try { repeat constructor } <;>\n      try norm_num <;>\n      try ring"
)

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
