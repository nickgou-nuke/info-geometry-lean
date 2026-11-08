with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

import re

# Add chiral_helper_1 before chiralStar_uOne_vOne
helper = "lemma chiral_helper_1 : (2:ℝ)⁻¹ * (-1 + -1) = -1 := by ring\n\n"

content = content.replace("theorem chiralStar_uOne_vOne", helper + "theorem chiralStar_uOne_vOne")

# In uOne_vOne and vOne_uOne, use chiral_helper_1 in simp
content = content.replace(
    "try norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>",
    "simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, chiral_helper_1] <;>"
)

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
