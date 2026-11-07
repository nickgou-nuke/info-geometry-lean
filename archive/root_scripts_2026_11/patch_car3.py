import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# Replace simple cases: <;> simp [Matrix.mul_apply, ...]
content = re.sub(
    r'<;>\s*simp\s*\[(.*?)Matrix\.mul_apply(.*?),(.*?)\]',
    r'<;> (simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]; simp [\1\3]; norm_num)',
    content
)

# Replace the 'first' blocks
#     first
#     | (simp [Matrix.mul_apply, Matrix.add_apply, eps0, iota0, Fin.sum_univ_eight]; norm_num)
#     | simp [Matrix.mul_apply, Matrix.add_apply, eps0, iota0, Fin.sum_univ_eight]
def repl_first(m):
    # m.group(1) is the content of the `first | ...` block
    return "(simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]; simp [gam0, gam1, gam2, eps0, eps1, eps2, iota0, iota1, iota2, fermionParity, deRhamDirac, Fin.sum_univ_eight]; norm_num)"

content = re.sub(
    r'\(\s*first\s*\|\s*\(simp \[.*?\]; norm_num\)\s*\|\s*simp \[.*?\]\s*\)',
    repl_first,
    content,
    flags=re.DOTALL
)

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
