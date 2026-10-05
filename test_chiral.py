with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

import re

# I will just write a python script to replace chiralStar_uOne_vOne body.
target = """theorem chiralStar_uOne_vOne : chiralStar uOne vOne = -rhoPlus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoPlus, entryZero, entryOne, entryI] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul]"""

replacement = """theorem chiralStar_uOne_vOne : chiralStar uOne vOne = -rhoPlus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [chiralStar, half, uOne, vOne, rhoPlus, entryZero, entryOne, entryI]
    try apply Quaternion.ext
    sorry
  · sorry
  · sorry
  · sorry"""

content = content.replace(target, replacement)

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)

