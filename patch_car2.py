import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# The original has:
# | (simp only [Matrix.mul_apply] <;> simp [gam0, eps0, iota0, Fin.sum_univ_eight]; norm_num)
# We want to change the inner simp to include Matrix.add_apply etc.
content = content.replace('; norm_num', '; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply]; norm_num')

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
