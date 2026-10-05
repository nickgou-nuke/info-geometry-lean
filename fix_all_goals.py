import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

universal_block = """  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [deRhamDirac, fermionParity]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply]
    simp only [gam0, gam1, gam2]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply]
    simp only [eps0, eps1, eps2, iota0, iota1, iota2]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]
    simp
    try norm_num
  }"""

# Find all blocks starting with `ext i j; fin_cases i <;> fin_cases j`
# and going until the closing `}`
content = re.sub(
    r'  ext i j; fin_cases i <;> fin_cases j\s*\n\s*all_goals \{.*?\n  \}',
    universal_block,
    content,
    flags=re.DOTALL
)

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
