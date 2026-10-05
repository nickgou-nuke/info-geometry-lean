import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

def repl_proof(m):
    text = m.group(0)
    args = re.search(r'simp\s*\[(.*?)\]', text)
    if not args:
        return text
    
    arg_list = [a.strip() for a in args.group(1).split(',')]
    
    defs1 = [a for a in arg_list if a in ['deRhamDirac', 'fermionParity', 'gam0', 'gam1', 'gam2']]
    mats = [a for a in arg_list if 'Matrix.' in a or 'Fin.sum' in a]
    defs2 = [a for a in arg_list if a not in defs1 and a not in mats]
    
    mats_str = "Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight"
    
    out = "  ext i j; fin_cases i <;> fin_cases j\n  all_goals {\n"
    if defs1:
        out += f"    simp only [{', '.join(defs1)}]\n"
    out += f"    simp only [{mats_str}]\n"
    if defs2:
        out += f"    simp only [{', '.join(defs2)}]\n"
    out += "    simp\n  }\n"
    
    return out

content = re.sub(r'  ext i j; fin_cases i <;> fin_cases j <;> .*?\n', repl_proof, content)

content = re.sub(r'  ext i j; fin_cases i <;> fin_cases j <;> \(\s*first.*?\n\s*\)', repl_proof, content, flags=re.DOTALL)

# Let's fix the explicit show in deRhamDirac_sq
content = re.sub(r'ext i j; fin_cases i <;> fin_cases j <;> \(\s*first.*?norm_num.*?\)', lambda m: repl_proof(m), content, flags=re.DOTALL)

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
