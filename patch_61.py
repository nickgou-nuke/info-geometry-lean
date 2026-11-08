with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

import re

fin_cases_block = """  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, chiralCoordinates,
      chiralZornProductCoordinates, half, uPlus, uMinus, uOne, uTwo, uThree,
      vOne, vTwo, vThree, rhoPlus, rhoMinus, entryOne, entryZero,
      entryI, entryJ, entryK] <;>
    ext <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    try ring"""

content = re.sub(
    r'  fin_cases i <;> fin_cases j <;>\n    simp \[chiralStar, chiralCoordinates,.*?\n      try ring',
    fin_cases_block, content, flags=re.DOTALL
)

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
