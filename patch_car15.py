import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# Fix gam0_sq
content = content.replace(
'''theorem gam0_sq : gam0 * gam0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]''',
'''theorem gam0_sq : gam0 * gam0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [gam0]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''
)

# Fix gam1_sq
content = content.replace(
'''theorem gam1_sq : gam1 * gam1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]''',
'''theorem gam1_sq : gam1 * gam1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [gam1]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''
)

# Fix gam2_sq
content = content.replace(
'''theorem gam2_sq : gam2 * gam2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]''',
'''theorem gam2_sq : gam2 * gam2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [gam2]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''
)

# Fix gam0_gam1_anticomm
content = content.replace(
'''theorem gam0_gam1_anticomm : gam0 * gam1 + gam1 * gam0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]''',
'''theorem gam0_gam1_anticomm : gam0 * gam1 + gam1 * gam0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [gam0, gam1]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''
)

# Fix gam1_gam2_anticomm
content = content.replace(
'''theorem gam1_gam2_anticomm : gam1 * gam2 + gam2 * gam1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]''',
'''theorem gam1_gam2_anticomm : gam1 * gam2 + gam2 * gam1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [gam1, gam2]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''
)

# Fix gam2_gam0_anticomm
content = content.replace(
'''theorem gam2_gam0_anticomm : gam2 * gam0 + gam0 * gam2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]''',
'''theorem gam2_gam0_anticomm : gam2 * gam0 + gam0 * gam2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [gam2, gam0]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''
)

# Fix deRhamDirac_sq
content = re.sub(
    r'rw \[show \(1 \+ 1 \+ 1 : Mat8\) = \(3 : ℝ\) • \(1 : Mat8\) by\s*ext i j; fin_cases i <;> fin_cases j <;> \([\s\S]*?\)\]',
'''rw [show (1 + 1 + 1 : Mat8) = (3 : ℝ) • (1 : Mat8) by
          ext i j; fin_cases i <;> fin_cases j
          all_goals {
            simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply]
            try norm_num
          }]''',
    content
)

# Fix fermionParity_anticomm_deRhamDirac
content = content.replace(
'''theorem fermionParity_anticomm_deRhamDirac :
    fermionParity * deRhamDirac + deRhamDirac * fermionParity = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]''',
'''theorem fermionParity_anticomm_deRhamDirac :
    fermionParity * deRhamDirac + deRhamDirac * fermionParity = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [fermionParity, deRhamDirac]
    simp only [gam0, gam1, gam2]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''
)

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
