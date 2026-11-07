import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# I will just replace the bad block inside fermionParity_anticomm_deRhamDirac
bad_block = '''theorem fermionParity_anticomm_deRhamDirac :
    fermionParity * deRhamDirac + deRhamDirac * fermionParity = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [fermionParity, deRhamDirac]
    simp only [gam0, gam1, gam2]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''

good_block = '''theorem fermionParity_anticomm_deRhamDirac :
    fermionParity * deRhamDirac + deRhamDirac * fermionParity = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]
    simp only [fermionParity, deRhamDirac]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]
    simp only [gam0, gam1, gam2]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]'''

content = content.replace(bad_block, good_block)

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
