import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# We will completely overwrite the proofs of the matrix equalities.
# Any theorem block starting with `ext i j; fin_cases i <;> fin_cases j <;>`
# will be replaced.

def repl_proof(m):
    # m.group(1) is the rest of the line, which has the simp.
    # we need to find what it was simplifying.
    args = re.search(r'simp\s*\[(.*?)\]', m.group(1))
    if not args:
        return m.group(0)
    
    arg_list = [a.strip() for a in args.group(1).split(',')]
    
    defs1 = [a for a in arg_list if a in ['deRhamDirac', 'gam0', 'gam1', 'gam2']]
    mats = [a for a in arg_list if 'Matrix.' in a or 'Fin.sum' in a]
    defs2 = [a for a in arg_list if a not in defs1 and a not in mats]
    
    # We always include these structural ones if they are around.
    # Actually, we know exactly what mats are needed for 8x8 matrices.
    mats_str = "Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight"
    
    # We will build an all_goals block
    out = "  ext i j; fin_cases i <;> fin_cases j\n  all_goals {\n"
    if defs1:
        out += f"    simp only [{', '.join(defs1)}]\n"
    out += f"    simp only [{mats_str}]\n"
    if defs2:
        out += f"    simp only [{', '.join(defs2)}]\n"
    out += "    simp\n  }\n"
    
    return out

# Replace single-line proofs
content = re.sub(r'  ext i j; fin_cases i <;> fin_cases j <;> .*?\n', repl_proof, content)

# But what about the `first | ...` proofs?
# e.g. car00:
#   ext i j; fin_cases i <;> fin_cases j <;> (
#     first
#     | (simp [Matrix.mul_apply, Matrix.add_apply, eps0, iota0, Fin.sum_univ_eight]; norm_num)
#     | simp [Matrix.mul_apply, Matrix.add_apply, eps0, iota0, Fin.sum_univ_eight]
#   )
# We can replace them explicitly using a similar trick.
content = re.sub(r'  ext i j; fin_cases i <;> fin_cases j <;> \(\s*first.*?simp\s*\[(.*?)\];.*?\)\n', 
                 lambda m: repl_proof(re.match(r'  ext i j; fin_cases i <;> fin_cases j <;> simp \[' + m.group(1) + '\]\n', f"  ext i j; fin_cases i <;> fin_cases j <;> simp [{m.group(1)}]\n")),
                 content, flags=re.DOTALL)

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
