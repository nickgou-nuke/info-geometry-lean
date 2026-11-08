with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

import re

def replacer(match):
    return """  fin_cases i <;> fin_cases j
  all_goals {
    simp [chiralStar, half, uOne, vOne, rhoPlus, rhoMinus, entryZero, entryOne, entryI]
    try apply Quaternion.ext
    try field_simp
    try ring
    try norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  }"""

# Replace all fin_cases i <;> fin_cases j <;> simp ... <;> try apply Quaternion.ext <;> ... <;> try trivial
# wait, there are too many variants. Let's just checkout the file to the initial state!
