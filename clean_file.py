import re

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

# Remove all chiral_helper_1 declarations
content = re.sub(r'lemma chiral_helper_1 : \(2:ℝ\)⁻¹ \* \(-1 \+ -1\) = -1 := by ring\n*', '', content)

# Fix the blocks for chiralStar_uOne_vOne (which is around line 1136)
uOne_vOne = """theorem chiralStar_uOne_vOne : chiralStar uOne vOne = -rhoPlus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoPlus, entryZero, entryOne, entryI] <;>
    try apply Quaternion.ext <;>
    try rw [Quaternion.ext_iff] <;>
    try constructor <;> try constructor <;> try constructor <;>
    try norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    try ring"""

content = re.sub(
    r'theorem chiralStar_uOne_vOne : chiralStar uOne vOne = -rhoPlus := by.*?try ring',
    uOne_vOne, content, flags=re.DOTALL
)

vOne_uOne = """theorem chiralStar_vOne_uOne : chiralStar vOne uOne = -rhoMinus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoMinus, entryZero, entryOne, entryI] <;>
    try apply Quaternion.ext <;>
    try rw [Quaternion.ext_iff] <;>
    try constructor <;> try constructor <;> try constructor <;>
    try norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    try ring"""

content = re.sub(
    r'theorem chiralStar_vOne_uOne : chiralStar vOne uOne = -rhoMinus := by.*?try ring',
    vOne_uOne, content, flags=re.DOTALL
)

line61 = """theorem chiralCoordinateGamma_equiv (x : ChiralCayley) (p q : ChiralCayley × ChiralCayley) :
    chiralCoordinatesEquiv (chiralCoordinateGamma (chiralCoordinatesEquiv.symm x) (chiralCayleyPairEquiv.symm p)) =
      chiralCayleyGamma x p := by
  -- Not showing the top part since we only want to patch the fin_cases block
"""

# Let's just replace the fin_cases block directly
fin_cases_block = """  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, chiralCoordinates,
      chiralZornProductCoordinates, half, uPlus, uMinus, uOne, uTwo, uThree,
      vOne, vTwo, vThree, rhoPlus, rhoMinus, entryOne, entryZero,
      entryI, entryJ, entryK] <;>
    try apply Quaternion.ext <;>
    try rw [Quaternion.ext_iff] <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    try constructor <;> try constructor <;> try constructor <;> try constructor <;>
    try ring_nf <;> try ring"""

content = re.sub(
    r'  fin_cases i <;> fin_cases j <;>\n    simp \[chiralStar, chiralCoordinates,.*?\n      try ring',
    fin_cases_block, content, flags=re.DOTALL
)

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
