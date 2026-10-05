import re

file_path = "lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean"
with open(file_path, "r") as f:
    content = f.read()

# First, restore the proof structure to use <;> so we don't have all_goals errors
content = content.replace("set_option pp.all true\ntheorem chiralStar_uOne_vOne", "theorem chiralStar_uOne_vOne")
content = re.sub(r"theorem chiralStar_uOne_vOne.*?exact chiral_helper_1\n", """theorem chiralStar_uOne_vOne : chiralStar uOne vOne = -rhoPlus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoPlus, entryZero, entryOne, entryI] <;>
    try apply Quaternion.ext <;>
    try rw [Quaternion.ext_iff] <;>
    try constructor <;> try constructor <;> try constructor <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    try change (2:ℝ)⁻¹ * (-1 + -1) = -1 <;>
    try ring
""", content, flags=re.DOTALL)

content = re.sub(r"theorem chiralStar_vOne_uOne.*?try ring_nf <;> try ring <;> try linarith <;> try norm_num\n", """theorem chiralStar_vOne_uOne : chiralStar vOne uOne = -rhoMinus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoMinus, entryZero, entryOne, entryI] <;>
    try apply Quaternion.ext <;>
    try rw [Quaternion.ext_iff] <;>
    try constructor <;> try constructor <;> try constructor <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    try change (2:ℝ)⁻¹ * (-1 + -1) = -1 <;>
    try ring
""", content, flags=re.DOTALL)

with open(file_path, "w") as f:
    f.write(content)

