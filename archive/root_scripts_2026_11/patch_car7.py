with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    text = f.read()

import re

def repl(m):
    args = m.group(1)
    if 'Matrix.mul_apply' in args:
        return f"(simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]; simp [{args}]; try norm_num)"
    return m.group(0)

# match `simp [...]`
text = re.sub(r'simp\s*\[(.*?)\]', repl, text)

# cleanup the `first | (...) | (...)` because now it's `first | ((simp only...)) | ((simp only...))`
text = text.replace('; norm_num); norm_num', '; norm_num)')
text = text.replace('try norm_num); norm_num', 'try norm_num)')

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(text)
