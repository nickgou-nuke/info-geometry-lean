import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# For lines with single simp
def repl_single(m):
    # m.group(1) is before Matrix.mul_apply
    # m.group(2) is between Matrix.mul_apply and the end bracket
    # we just split the simp into simp only [...] then simp [original contents] then try norm_num
    inside = m.group(1)
    return f"<;> (simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]; simp [{inside}]; try norm_num)"

content = re.sub(r'<;>\s*simp\s*\[(.*?)\]', repl_single, content)

# But wait, the original file has things like:
# first | (simp [Matrix.mul_apply, Matrix.add_apply, eps0, iota0, Fin.sum_univ_eight]; norm_num) | simp [...]
# We can just run a python script that matches `simp [args]` and replaces it.
