import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# We'll process line by line
lines = content.split('\n')
out = []
defined_symbols = set(['eps0', 'eps1', 'eps2', 'iota0', 'iota1', 'iota2'])

i = 0
while i < len(lines):
    line = lines[i]
    
    if line.startswith('def gam0'): defined_symbols.update(['gam0', 'gam1', 'gam2'])
    if line.startswith('def deRhamDirac'): defined_symbols.add('deRhamDirac')
    if line.startswith('def fermionParity'): defined_symbols.add('fermionParity')
    
    if 'ext i j; fin_cases i <;> fin_cases j' in line:
        out.append('  ext i j; fin_cases i <;> fin_cases j')
        
        is_all_goals = False
        if i + 1 < len(lines) and 'all_goals {' in lines[i+1]:
            j = i + 1
            while j < len(lines) and '}' not in lines[j]:
                j += 1
            i = j
        elif '<;> (' in line or '<;> \\(' in line:
            j = i + 1
            while j < len(lines) and ')' not in lines[j]:
                j += 1
            i = j
            
        out.append("  all_goals {")
        
        if 'deRhamDirac' in defined_symbols or 'fermionParity' in defined_symbols:
            l = []
            if 'deRhamDirac' in defined_symbols: l.append('deRhamDirac')
            if 'fermionParity' in defined_symbols: l.append('fermionParity')
            out.append(f"    simp only [{', '.join(l)}]")
            out.append("    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply]")
            
        if 'gam0' in defined_symbols:
            out.append("    simp only [gam0, gam1, gam2]")
            out.append("    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply]")
            
        # ALWAYS DO MATRIX OP BEFORE EPS0
        out.append("    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply]")
        out.append("    simp only [eps0, eps1, eps2, iota0, iota1, iota2]")
        out.append("    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]")
        out.append("    simp")
        out.append("    try norm_num")
        out.append("  }")
        
    else:
        out.append(line)
            
    i += 1

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write('\n'.join(out))
