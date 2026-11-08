import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# For gam0_sq, gam1_sq, gam2_sq, etc., we want to just do:
# ext i j; fin_cases i <;> fin_cases j; simp [gam0, eps0, iota0, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_eight]; norm_num

# Wait, `gam0` might use `eps0`, etc. Let's just define a super simp list.
simp_list = "[gam0, gam1, gam2, eps0, eps1, eps2, iota0, iota1, iota2, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]"

# We can replace all the big tactic blocks. They look like:
#   ext i j; fin_cases i <;> fin_cases j <;> (
#     first
#     | (simp only [Matrix.mul_apply] <;> simp [gam0, eps0, iota0, Fin.sum_univ_eight]; norm_num)
#     | simp only [Matrix.mul_apply] <;> simp [gam0, eps0, iota0, Fin.sum_univ_eight]
#   )

pattern = r"ext i j; fin_cases i <;> fin_cases j <;> \(\n\s*first\n\s*\|[^\n]*\n\s*\|[^\n]*\n\s*\)"

def repl(m):
    return "ext i j; fin_cases i <;> fin_cases j <;> simp " + simp_list + " <;> norm_num"

content = re.sub(pattern, repl, content)

# Also there's one with `ext i j; fin_cases i <;> fin_cases j <;> ( ... )` for anti-commutation, let's just make it broad.
pattern2 = r"ext i j; fin_cases i <;> fin_cases j <;> \(\n\s*first\n\s*\| \([^)]*\)\n\s*\| [^\n]*\n\s*\)"
content = re.sub(pattern2, repl, content)

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)

