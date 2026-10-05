with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

lemma_code = """
lemma chiral_helper_1 : (2:ℝ)⁻¹ * (-1 + -1) = -1 := by ring
"""

content = content.replace("theorem chiralStar_uOne_vOne", lemma_code + "\ntheorem chiralStar_uOne_vOne")

content = content.replace(
    "    try apply Quaternion.ext <;>\n      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try { repeat constructor } <;>\n      try norm_num <;>\n      try ring",
    "    try apply Quaternion.ext <;>\n      try rw [Quaternion.ext_iff] <;>\n      try { repeat constructor } <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul, chiral_helper_1] <;>\n      try ring"
)

content = content.replace(
    "    try apply Quaternion.ext <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try { repeat constructor } <;>\n      try ring",
    "    try apply Quaternion.ext <;>\n      try rw [Quaternion.ext_iff] <;>\n      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,\n        Quaternion.imK_mul] <;>\n      try { repeat constructor } <;>\n      try ring"
)

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
